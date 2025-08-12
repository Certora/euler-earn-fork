//Based on generic ERC4626 specitication: https://github.com/Certora/Examples/blob/master/DEFI/ERC4626/certora/specs/ERC4626.spec

import "Range.spec";
using Token0 as Token0;
using ERC20Helper as ERC20Helper;
using EthereumVaultConnector as EVC;

methods {
    function _._msgSender() internal with (env e) => e.msg.sender expect address; //ignoring EVC compatibility

     function SafeERC20.safeTransfer(address token,address to,uint256 value) internal with (env e) 
        => tokenTransferFromToCVL(e,token,calledContract,to,value); 
    function EulerEarn.HOOK_after_withdrawStrategy(uint256 assets) internal => CVL_after_withdrawStrategy(assets);
    function EulerEarn.HOOK_after_accrueInterest() internal => CVL_after_accrueInterest();

    function EVC.getAccountOwner(address) external returns address envfree;
    function config_(address) external returns EulerEarnHarness.MarketConfig envfree; 
    function virtualAmount() external returns uint256 envfree;
    function permit2Address() external returns address envfree;
    function feeRecipient() external returns address envfree;
    function withdrawQGetAt(uint256) external returns address envfree;
    function name() external returns string envfree;
    function symbol() external returns string envfree;
    function decimals() external returns uint8 envfree;
    function asset() external returns address envfree;
    function fees() external returns uint256 envfree;
    function lostAssets() external returns uint256 envfree;
    function lastTotalAssets() external returns uint256 envfree;
    function realTotalAssets() external returns uint256 envfree;
    function fee() external returns uint96 envfree;
    function wad() external returns uint256 envfree;
    function withdrawQueueLength() external returns uint256 envfree;
    function ERC20Helper.totalSupply(address) external returns uint256 envfree;
    function totalSupply() external returns uint256 envfree;
    function balanceOf(address) external returns uint256 envfree;
    function reentrancyGuardEntered() external returns bool envfree;

    function approve(address,uint256) external returns bool;
    function deposit(uint256,address) external;
    function mint(uint256,address) external;
    function withdraw(uint256,address,address) external;
    function redeem(uint256,address,address) external;
    function totalAssets() external returns uint256 envfree;
    function convertToShares(uint256) external returns uint256 envfree;
    function convertToAssets(uint256) external returns uint256 envfree;
    function previewDeposit(uint256) external returns uint256 envfree;
    function previewMint(uint256) external returns uint256 envfree;
    function previewWithdraw(uint256) external returns uint256 envfree;
    function previewRedeem(uint256) external returns uint256 envfree;
    function maxDeposit(address) external returns uint256 envfree;
    function maxMint(address) external returns uint256 envfree;
    function maxWithdraw(address) external returns uint256 envfree;
    function maxRedeem(address) external returns uint256 envfree;
    function permit(address,address,uint256,uint256,uint8,bytes32,bytes32) external;
    function DOMAIN_SEPARATOR() external returns bytes32;
    function Token0.balanceOf(address) external returns uint256 envfree;
    function Token0.allowance(address, address) external returns uint256 envfree;
    function Token0.transferFrom(address,address,uint256) external returns bool;
    function allowance(address,address) external returns uint256 envfree;
}

function tokenTransferFromToCVL(env e,address token,address from, address to, uint256 value) {
    if (token == Token0) {
        Token0._transfer(e,from, to, value);
        return;
    }
    require false, "this should only be called on Token0";
}

function safeAssumptions(env e) {
    require currentContract != asset(); // Although this is not disallowed, we assume the contract's underlying asset is not the contract itself
    requireInvariant totalSupplyIsSumOfBalances();
    require msgSender(e) != currentContract;  // This is proved by rule noDynamicCalls
    requireInvariant feeInRange();
    requireInvariant configBalanceAndTotalSupply(withdrawQGetAt(0));   
    requireInvariant noAssetsOnEuler();
    
    uint256 fees;
    uint256 totalAssets; 
    uint256 lostAssets;
    uint256 totalSupply = totalSupply();
    (fees,totalAssets,lostAssets) =  _accruedFeeAndAssets(e);
    require totalAssets >= fees + totalSupply, "proven in TotalAssetsMoreThanSupplyAndFees - in different cases"; 
    require totalAssets <= 2^128, "reasonable value for totalAssets";
    require totalSupply <= 2^128, "reasonable value for totalSupply";
    require lostAssets <= 2^128, "reasonable value for lostAssets";
}

ghost mathint sumOfBalances {
    init_state axiom sumOfBalances == 0;
}

hook Sstore _balances[KEY address addy] uint256 newValue (uint256 oldValue)  {
    sumOfBalances = sumOfBalances + newValue - oldValue;
}

hook Sload uint256 val _balances[KEY address addy]  {
    require sumOfBalances >= val;
}

// Verified
invariant totalSupplyIsSumOfBalances()
    totalSupply() == sumOfBalances;


// Verified
invariant noAssetsOnEuler()
    Token0.balanceOf(currentContract) == 0
    {   
        preserved withdraw(uint256 assets, address receiver, address owner) with (env e) {
            require receiver != currentContract;
            require owner != currentContract;
            safeAssumptions(e);
        }
        preserved redeem(uint256 assets, address receiver, address owner) with (env e) {
            require receiver != currentContract;
            require owner != currentContract;
            safeAssumptions(e);
        }
        preserved with (env e) {
            safeAssumptions(e);
        }
    }

/// solvency properties.

// Verified https://prover.certora.com/output/5771024/455e0433202940aebcd4aa94b939561e/
rule propertiesAfterAccrue() {
    require totalAssets() >= totalSupply() + fees();
    env e;
    _accrueInterest(e);
    assert fees() == 0; 
    assert totalAssets() >= totalSupply() + fees();
}

function CVL_after_accrueInterest() {
    assert totalAssets() >= totalSupply() + fees();
}

// Main solvency invariant -- broken up into the different cases for different operations:

invariant TotalAssetsMoreThanSupplyAndFees()
    totalAssets() >= totalSupply() + fees()
    //filter out withdraw and redeem - those are proven in a different rule - solvency in Internal Withdraw
    filtered {
    f -> (f.selector != sig:withdraw(uint256,address,address).selector &&
          f.selector != sig:redeem(uint256,address,address).selector)
    }
    {
        preserved with (env e) {
            safeAssumptions(e);
            require withdrawQueueLength() == 1;
        }
    }

// prob can delete these if above verifies. 

// // Verified https://prover.certora.com/output/5771024/3515c79d5e9a44349f06b12c61ef5221/
// invariant TotalAssetsMoreThanSupplyAndFeesDeposit()
//     totalAssets() >= totalSupply() + fees()
//     filtered {
//     f -> f.selector == sig:deposit(uint256,address).selector
//     }
//     {
//         preserved with (env e) {
//             safeAssumptions(e);
//             require withdrawQueueLength() == 1;
//         }
//     }

// // Verified https://prover.certora.com/output/5771024/faf5c9e75afa4bb185bae3ed323c6612/
// invariant TotalAssetsMoreThanSupplyAndFeesMint()
//     totalAssets() >= totalSupply() + fees()
//     filtered {
//     f -> f.selector == sig:mint(uint256,address).selector
//     }
//     {
//         preserved with (env e) {
//             safeAssumptions(e);
//             require withdrawQueueLength() == 1;
//         }
//     }


ghost uint256 totalSupplyGhost;
ghost uint256 assetsInGhost;
ghost uint256 totalAssetsAfterWithdrawStrategy;

// Hook summaries that serve as lemmas for the solvencyInInternalWithdraw rule 
// this is only useful if run with multi_assert_check = true 
function CVL_after_withdrawStrategy(uint256 assetsIn) {
    // There is some bug with the summaries (see ticket -- so I am using asstsInGhost instead of assetsIn input)

    // not sure about these still -- need to think
    assert totalSupply() == totalSupplyGhost,
    "total supply does not change"; //verified 
    assert Token0.balanceOf(currentContract) == assetsInGhost, 
    "after withdraw stategy the assets are moved to Euler"; // verified
    uint256 totalAssetsNow = totalAssets();
    // assert totalAssetsNow + Token0.balanceOf(currentContract) >= totalSupply(), 
    // "The sum of assets moved to Euler + totalAssets in vaults >= totalSupply"; //verified
    totalAssetsAfterWithdrawStrategy = totalAssetsNow;
}

// verified https://prover.certora.com/output/5771024/d1f58762c7934808b936bd1a41fb15d9/ (most revent proof with less approximations)
rule solvencyInInternalWithdraw() {
    // simulating the internal _withdraw in a call from the external withdraw
    env e;
    address caller;
    address receiver;
    address owner;
    uint256 assets;
    uint256 shares;
    safeAssumptions(e); 

    require withdrawQueueLength() == 1; 
    address withdrawQueueFirstVault = withdrawQGetAt(0);
    
    require caller != withdrawQueueFirstVault;
    require receiver != withdrawQueueFirstVault;
    require owner != withdrawQueueFirstVault;
    require receiver != currentContract; 
    require caller != currentContract;
    require owner != currentContract;
    require currentContract != withdrawQueueFirstVault;

    uint256 totalAssetsPre; 
    uint256 feesPre;
    uint256 lostAssetsPre;
    uint256 totalSupplyPre = totalSupply();
    (feesPre,totalAssetsPre,lostAssetsPre) =  _accruedFeeAndAssets(e); // 6 non-linear ops 
    require totalSupplyGhost == totalSupplyPre;
    require assetsInGhost == assets;

    uint256 lastTotalAssetsPre = lastTotalAssets();
    require totalAssetsPre >= totalSupplyPre + feesPre, "solvent before";
    require lastTotalAssetsPre == totalAssetsPre, "_withdraw is called after _accrueInterest";
    assert feesPre == 0; // verified

    bool assetSharesRelationInWithdraw = ( shares == _convertToSharesWithTotals(e,assets, totalSupplyPre, lastTotalAssetsPre, Math.Rounding.Ceil) ); // 2 non-linear ops
    bool assetSharesRelationInRedeem = ( assets == _convertToAssetsWithTotals(e,shares, totalSupplyPre, lastTotalAssetsPre, Math.Rounding.Floor)); // 2 non-linear ops
    require assetSharesRelationInWithdraw || assetSharesRelationInRedeem,
        "internal withdraw is called either in the external withdraw or the external redeem";

    assert shares <= assets; // verified

    _withdraw(e,caller,receiver,owner,assets,shares); // 22 non-linear ops -> cvlDispatchMaxWithdraw - 4, cvlDispatchPreviewRedeem - 4, CVL_after_withdrawStrategy - 6 

    uint256 totalAssetsPost; 
    uint256 feesPost;
    uint256 lostAssetsPost;
    uint256 totalSupplyPost = totalSupply();
    (feesPost,totalAssetsPost,lostAssetsPost) =  _accruedFeeAndAssets(e); // 6 non-linear ops 
    uint256 lastTotalAssetsPost = lastTotalAssets(); 
    
    assert totalAssetsPost == totalAssetsAfterWithdrawStrategy; // verified
    assert totalSupplyPost == assert_uint256(totalSupplyPre - shares); // verified
    assert Token0.balanceOf(currentContract) == 0; // verified
    assert lastTotalAssetsPost == assert_uint256(lastTotalAssetsPre - assets); // verified
    uint256 totalInterest = assert_uint256(totalAssetsPost-lastTotalAssetsPost); // verified
    // uint256 feeAssets = feeAssetsFromTotalInterest[totalInterest]; //using ghost as is used in the summary, guaranteed to satisfy feeAssets<=totalInterest, originally this is totalInterest.mulDiv(fee, WAD);
    uint256 feeAssets = cvlMulDiv(totalInterest,fee(), wad()); //original implementation
    assert feeAssets <= totalInterest; // Verified
    assert assert_uint256(totalAssetsPost-feeAssets) >= totalSupplyPost;
    assert require_uint256(assert_uint256(totalAssetsPost-feeAssets)+virtualAmount()) >= require_uint256(totalSupplyPost+virtualAmount());
    assert feesPost <= feeAssets;
    assert feesPost <= totalInterest;
    assert totalAssetsPost >= totalSupplyPost + feesPost, "solvent after"; // verified if we assume feesPost <= totalInterest 
}

// Verified 
rule conversionOfZero {
    uint256 convertZeroShares = convertToAssets(0);
    uint256 convertZeroAssets = convertToShares(0);

    assert convertZeroShares == 0,
        "converting zero shares must return zero assets";
    assert convertZeroAssets == 0,
        "converting zero assets must return zero shares";
}

// Verified with caching summary (see above) or with CONSTANT summary
rule convertToAssetsWeakAdditivity() {
    uint256 sharesA; uint256 sharesB;
    uint256 assetsA = convertToAssets(sharesA);
    uint256 assetsB = convertToAssets(sharesB);
    uint256 sharesAplusB = require_uint256(sharesA + sharesB);
    uint256 assetsAplusB = convertToAssets(sharesAplusB);
    require sharesA + sharesB < max_uint128
         && assetsA + assetsB < max_uint256
         && assetsAplusB < max_uint256;
    assert assetsA + assetsB <= assetsAplusB,
        "converting sharesA and sharesB to assets then summing them must yield a smaller or equal result to summing them then converting";
}

// Verified with caching summary
rule convertToSharesWeakAdditivity() {
    uint256 assetsA; uint256 assetsB;
    uint256 sharesA = convertToShares(assetsA);
    uint256 sharesB = convertToShares(assetsB);
    uint256 assetsAplusB = require_uint256(assetsA+assetsB);
    uint256 sharesAplusB = convertToShares(assetsAplusB);
    require assetsA + assetsB < max_uint128
         && sharesA + sharesB < max_uint256
         && sharesAplusB < max_uint256;
    assert sharesA + sharesB <= sharesAplusB,
        "converting assetsA and assetsB to shares then summing them must yield a smaller or equal result to summing them then converting";
}

// Verified
rule conversionWeakMonotonicity {
    uint256 smallerShares; uint256 largerShares;
    uint256 smallerAssets; uint256 largerAssets;

    assert smallerShares < largerShares => convertToAssets(smallerShares) <= convertToAssets(largerShares),
        "converting more shares must yield equal or greater assets";
    assert smallerAssets < largerAssets => convertToShares(smallerAssets) <= convertToShares(largerAssets),
        "converting more assets must yield equal or greater shares";
}

// Verified
rule conversionWeakIntegrity() {
    uint256 sharesOrAssets;
    assert convertToShares(convertToAssets(sharesOrAssets)) <= sharesOrAssets,
        "converting shares to assets then back to shares must return shares less than or equal to the original amount";
    assert convertToAssets(convertToShares(sharesOrAssets)) <= sharesOrAssets,
        "converting assets to shares then back to assets must return assets less than or equal to the original amount";
}

// Verified
rule underlyingCannotChange() 
{
    address originalAsset = asset();

    method f; env e; calldataarg args;
    f(e, args);

    address newAsset = asset();

    assert originalAsset == newAsset,
        "the underlying asset of a contract must not change";
}

// Verified -- not standard ERC4626 but specific to us, this is simple because config_(market).balance should equal market.balanceOf(currentContract)
invariant configBalanceAndTotalSupply(address market) 
    config_(market).balance <= ERC20Helper.totalSupply(market) 
    {
        preserved with(env e) {
            require msgSender(e) != currentContract;
            safeAssumptions(e);
        }
    }


// Verified on most recent verison (was violated before) https://prover.certora.com/output/5771024/75bb49eac8b34219bb9e177fcc25773a/
rule zeroDepositZeroShares(uint assets, address receiver){
    env e;

    uint shares = deposit(e,assets, receiver);

    assert shares == 0 <=> assets == 0;
}


// Verified https://prover.certora.com/output/5771024/9d68a0e5a30c454f9f0ca25cd10230f6/
rule redeemingAllValidity() { 
    address owner; 
    address feeRecipient = feeRecipient();
    require owner != feeRecipient;

    uint256 shares; require shares == balanceOf(owner);
    
    env e; safeAssumptions(e);
    redeem(e, shares, _, owner);
    uint256 ownerBalanceAfter = balanceOf(owner);
    assert ownerBalanceAfter == 0;
}

// Verified https://prover.certora.com/output/5771024/fdeec6302e9b429bb0b725f3d9fd22fe
invariant zeroAllowanceOnAssets(address user)
    // no alloownaces from current contract.
    Token0.allowance(currentContract, user) == 0 && currentContract.allowance(currentContract, user) == 0 {
        preserved with(env e) {
            require msgSender(e) != currentContract;
            safeAssumptions(e);
            require user != permit2Address(), "allownaces for permit2 behave differently.";
        }
    }

// Verified
rule onlyContributionMethodsReduceAssets(method f) {
    address user; require user != currentContract;
    uint256 userBalanceOfBefore = Token0.balanceOf(user);

    env e; 
    calldataarg args;
    safeAssumptions(e);

    f(e, args);

    uint256 userBalanceOfAfter = Token0.balanceOf(user);

    assert userBalanceOfBefore > userBalanceOfAfter =>
        (f.selector == sig:deposit(uint256,address).selector ||
         f.selector == sig:mint(uint256,address).selector ||
         f.contract == asset() || f.contract == currentContract),
        "a user's assets must not go down except on calls to contribution methods or calls directly to the asset.";
}

