//Based on generic ERC4626 specitication: https://github.com/Certora/Examples/blob/master/DEFI/ERC4626/certora/specs/ERC4626.spec

import "Range.spec";
using Token0 as Token0;
using ERC20Helper as ERC20Helper;
using EthereumVaultConnector as EVC;

methods {
    function _._msgSender() internal with (env e) => e.msg.sender expect address; //ignoring EVC compatibility
    // function _._accruedFeeAndAssets() internal with (env e) => _accruedFeeAndAssetsSummary(e) expect (uint256,uint256,uint256);
    // function EulerEarn.HOOK_after_accrueInterest() internal => CVL_after_accrueInterest();

    // the summary we had with nonAssembly in EulerEarnHarness was bad    
     function SafeERC20.safeTransfer(address token,address to,uint256 value) internal with (env e) 
        => tokenTransferFromToCVL(e,token,calledContract,to,value); 
    
    // function _._decimalsOffset() internal => 18 expect uint8; // TRYING 18 as a default value for decimal offset of underlying vaults.
    function EVC.getAccountOwner(address) external returns address envfree;
    function config_(address) external returns EulerEarnHarness.MarketConfig envfree; 
    function virtualAmount() external returns uint256 envfree;
    function permit2Address() external returns address envfree;
    function feeRecipient() external returns address envfree;
    function expectedSupplyAssets(address) external returns uint256 envfree;
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

// Any invariant proved anywhere can be added here.
// For solvency TotalAssetsMoreThanSupplyAndFeesElse -- we are not done proving it, but using it to test.
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

// allows us to make the summary below deterministic.
ghost mapping(uint256  => uint256) feeAssetsFromTotalInterest;
function _accruedFeeAndAssetsSummary(env e) returns (uint256,uint256,uint256) {
    uint256 lastTotalAssets = lastTotalAssets();
    uint256 lostAssets = lostAssets();
    uint256 realTotalAssets;
    uint256 totalSupply = totalSupply();
    
    if (withdrawQueueLength() == 0) {
        require realTotalAssets == 0;
    }
    else {
        address firstMarket = withdrawQGetAt(0);
        uint256 firstMarketExpectedSupplyAssets = expectedSupplyAssets(firstMarket);
        require realTotalAssets == firstMarketExpectedSupplyAssets;
    }

    uint256 newLostAssets;
    if (realTotalAssets < lastTotalAssets - lostAssets) {
        newLostAssets = require_uint256(lastTotalAssets - realTotalAssets);
    } else {
        newLostAssets = lostAssets;
    }
    uint256 newTotalAssets = require_uint256(realTotalAssets + newLostAssets);
    uint256 totalInterest = require_uint256(newTotalAssets - lastTotalAssets);
    uint256 feeAssets = feeAssetsFromTotalInterest[totalInterest];
    require feeAssets <= totalInterest; //instead of doing the mulDiv we just enforce this.

    uint256 feeShares = _convertToSharesWithTotals(e,feeAssets, totalSupply(), require_uint256(newTotalAssets - feeAssets), Math.Rounding.Floor);
    return (feeShares, newTotalAssets, newLostAssets);
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

function CVL_after_accrueInterest() {
    assert totalAssets() >= totalSupply() + fees();
}

// Main solvency invariant -- broken up into the different cases for different operations:
// first two cases - timeout 
invariant TotalAssetsMoreThanSupplyAndFeesWithdraw()
    totalAssets() >= totalSupply() + fees()
    filtered {
    f -> f.selector == sig:withdraw(uint256,address,address).selector
    }
    {
        preserved with (env e) {
            safeAssumptions(e);
            require withdrawQueueLength() == 1;
        }
    }

invariant TotalAssetsMoreThanSupplyAndFeesRedeem()
    totalAssets() >= totalSupply() + fees()
    filtered {
    f -> f.selector == sig:redeem(uint256,address,address).selector
    }
    {
        preserved with (env e) {
            safeAssumptions(e);
            require withdrawQueueLength() == 1;
        }
    }

// Verified https://prover.certora.com/output/5771024/3515c79d5e9a44349f06b12c61ef5221/
invariant TotalAssetsMoreThanSupplyAndFeesDeposit()
    totalAssets() >= totalSupply() + fees()
    filtered {
    f -> f.selector == sig:deposit(uint256,address).selector
    }
    {
        preserved with (env e) {
            safeAssumptions(e);
            require withdrawQueueLength() == 1;
        }
    }

// Verified https://prover.certora.com/output/5771024/faf5c9e75afa4bb185bae3ed323c6612/
invariant TotalAssetsMoreThanSupplyAndFeesMint()
    totalAssets() >= totalSupply() + fees()
    filtered {
    f -> f.selector == sig:mint(uint256,address).selector
    }
    {
        preserved with (env e) {
            safeAssumptions(e);
            require withdrawQueueLength() == 1;
        }
    }

// Verified https://prover.certora.com/output/5771024/47f4a8b0537942c29fe91664da88a13e/
invariant TotalAssetsMoreThanSupplyAndFeesElse()
    totalAssets() >= totalSupply() + fees()
    filtered {
    f -> !(f.selector == sig:withdraw(uint256,address,address).selector
      || f.selector == sig:redeem(uint256,address,address).selector
      || f.selector == sig:deposit(uint256,address).selector
      || f.selector == sig:mint(uint256,address).selector
      )
    }
    {
        preserved updateWithdrawQueue(uint256[] indexes) with (env e) {
            safeAssumptions(e);
            require withdrawQueueLength() == 1;
            require indexes.length != 0;
        }
        preserved with (env e) {
            safeAssumptions(e);
            require withdrawQueueLength() == 1;
        }
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

// timeout
rule totalsMonotonicity()
{
    method f; env e; calldataarg args;
    require !f.isView;
    require msgSender(e) != currentContract; 
    uint256 totalSupplyBefore = require_uint256(totalSupply() + fees());
    uint256 totalAssetsBefore = totalAssets();

    safeAssumptions(e);
    f(e, args);
    require withdrawQueueLength() >= 1, "ignore cases where the withdraw queue is emptied";

    uint256 totalSupplyAfter = require_uint256(totalSupply() + fees());
    uint256 totalAssetsAfter = totalAssets();
    
    // possibly assert totalSupply and totalAssets must not change in opposite directions
    assert totalSupplyBefore < totalSupplyAfter  <=> totalAssetsBefore < totalAssetsAfter,
        "if totalSupply changes by a larger amount, the corresponding change in totalAssets must remain the same or grow";
    assert totalSupplyAfter == totalSupplyBefore => totalAssetsBefore == totalAssetsAfter,
        "equal size changes to totalSupply must yield equal size changes to totalAssets";
}

// timeout
rule depositMonotonicity() {
    env e; storage start = lastStorage;

    uint256 smallerAssets; uint256 largerAssets;
    address receiver;
    require currentContract != msgSender(e) && currentContract != receiver; 

    safeAssumptions(e);

    deposit(e, smallerAssets, receiver);
    uint256 smallerShares = balanceOf(receiver) ;

    deposit(e, largerAssets, receiver) at start;
    uint256 largerShares = balanceOf(receiver) ;

    assert smallerAssets < largerAssets => smallerShares <= largerShares,
            "when supply tokens outnumber asset tokens, a larger deposit of assets must produce an equal or greater number of shares";
}

// Violated on original
// Verified on fix https://prover.certora.com/output/5771024/75bb49eac8b34219bb9e177fcc25773a/
rule zeroDepositZeroShares(uint assets, address receiver){
    env e;

    uint shares = deposit(e,assets, receiver);

    assert shares == 0 <=> assets == 0;
}

// timeout - because of call to both deposit and redeem (rules with just redeem timeout)
rule dustFavorsTheHouse(uint assetsIn )
{
    env e;
        
    require msgSender(e) != currentContract;
    safeAssumptions(e);
    uint256 totalSupplyBefore = totalSupply();

    uint userBalanceOfBefore = Token0.balanceOf(msgSender(e));

    uint shares = deposit(e,assetsIn, msgSender(e));
    uint assetsOut = redeem(e,shares,msgSender(e),msgSender(e));

    uint userBalanceOfAfter = Token0.balanceOf(msgSender(e));

    assert userBalanceOfAfter <= userBalanceOfBefore;
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

function callContributionMethods(env e, method f, uint256 assets, uint256 shares, address receiver) {
    if (f.selector == sig:deposit(uint256,address).selector) {
        deposit(e, assets, receiver);
    }
    if (f.selector == sig:mint(uint256,address).selector) {
        mint(e, shares, receiver);
    }
}

// Violated: https://prover.certora.com/output/5771024/a4623f525b0c4bae9a77ea0693ecaa6c/
rule contributingProducesShares(method f)
filtered {
    f -> f.selector == sig:deposit(uint256,address).selector
      || f.selector == sig:mint(uint256,address).selector
}
{
    env e; uint256 assets; uint256 shares;
    address contributor; require contributor == msgSender(e);
    address receiver;
    require currentContract != contributor
         && currentContract != receiver;

    require previewDeposit(assets) + balanceOf(receiver) <= max_uint256; // safe assumption because call to _mint will revert if totalSupply += amount overflows
    require shares + balanceOf(receiver) <= max_uint256; // same as above

    safeAssumptions(e);

    uint256 contributorAssetsBefore = Token0.balanceOf(contributor); //in assets
    uint256 receiverSharesBefore = balanceOf(receiver); //in shares

    callContributionMethods(e, f, assets, shares, receiver);

    uint256 contributorAssetsAfter = Token0.balanceOf(contributor);
    uint256 receiverSharesAfter = balanceOf(receiver);

    assert contributorAssetsBefore > contributorAssetsAfter <=> receiverSharesBefore < receiverSharesAfter, //maybe leq or geq
        "a contributor's assets must decrease if and only if the receiver's shares increase";
}


function callReclaimingMethods(env e, method f, uint256 assets, uint256 shares, address receiver, address owner) {
    if (f.selector == sig:withdraw(uint256,address,address).selector) {
        withdraw(e, assets, receiver, owner);
    }
    if (f.selector == sig:redeem(uint256,address,address).selector) {
        redeem(e, shares, receiver, owner);
    }
}
// Violated: https://prover.certora.com/output/5771024/a4623f525b0c4bae9a77ea0693ecaa6c/
rule reclaimingProducesAssets(method f)
filtered {
    f -> f.selector == sig:withdraw(uint256,address,address).selector
      || f.selector == sig:redeem(uint256,address,address).selector
}
{
    env e; uint256 assets; uint256 shares;
    address receiver; address owner;
    require currentContract != msgSender(e)
         && currentContract != receiver
         && currentContract != owner;

    safeAssumptions(e);

    uint256 ownerSharesBefore = balanceOf(owner);
    uint256 receiverAssetsBefore = Token0.balanceOf(receiver);

    callReclaimingMethods(e, f, assets, shares, receiver, owner);

    uint256 ownerSharesAfter = balanceOf(owner);
    uint256 receiverAssetsAfter = Token0.balanceOf(receiver);

    assert ownerSharesBefore > ownerSharesAfter <=> receiverAssetsBefore < receiverAssetsAfter,
        "an owner's shares must decrease if and only if the receiver's assets increase";
}
