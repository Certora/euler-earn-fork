// Based on generic ERC4626 specitication: https://github.com/Certora/Examples/blob/master/DEFI/ERC4626/certora/specs/ERC4626.spec

//// INVARIANT 
//// Token0.balanceOf(currentContract) == 0


import "setup/dispatching_EulerEarn.spec";
import "summaries/Math.spec";
using Token0 as Token0;

methods {
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

    function totalSupply() external returns uint256 envfree;
    function balanceOf(address) external returns uint256 envfree;

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

// Verified 
rule conversionOfZero {
    uint256 convertZeroShares = convertToAssets(0);
    uint256 convertZeroAssets = convertToShares(0);

    assert convertZeroShares == 0,
        "converting zero shares must return zero assets";
    assert convertZeroAssets == 0,
        "converting zero assets must return zero shares";
}

// Timeout
// should maybe hold - try
rule convertToAssetsWeakAdditivity() {
    uint256 sharesA; uint256 sharesB;
    require sharesA + sharesB < max_uint128
         && convertToAssets(sharesA) + convertToAssets(sharesB) < max_uint256
         && convertToAssets(require_uint256(sharesA + sharesB)) < max_uint256;
    assert convertToAssets(sharesA) + convertToAssets(sharesB) <= convertToAssets(require_uint256(sharesA + sharesB)),
        "converting sharesA and sharesB to assets then summing them must yield a smaller or equal result to summing them then converting";
}

// Timeout
rule convertToSharesWeakAdditivity() {
    uint256 assetsA; uint256 assetsB;
    require assetsA + assetsB < max_uint128
         && convertToAssets(assetsA) + convertToAssets(assetsB) < max_uint256
         && convertToAssets(require_uint256(assetsA + assetsB)) < max_uint256;
    assert convertToAssets(assetsA) + convertToAssets(assetsB) <= convertToAssets(require_uint256(assetsA + assetsB)),
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

// Timeout
// try 
rule depositMonotonicity() {
    env e; storage start = lastStorage;

    uint256 smallerAssets; uint256 largerAssets;
    address receiver;
    require currentContract != msgSender(e) && currentContract != receiver; 

    safeAssumptions(e, msgSender(e), receiver);

    deposit(e, smallerAssets, receiver);
    uint256 smallerShares = balanceOf(receiver) ;

    deposit(e, largerAssets, receiver) at start;
    uint256 largerShares = balanceOf(receiver) ;

    assert smallerAssets < largerAssets => smallerShares <= largerShares,
            "when supply tokens outnumber asset tokens, a larger deposit of assets must produce an equal or greater number of shares";
}

// Violated: https://prover.certora.com/output/5771024/b15799cc3bb74f438c991b341f2ee470/ (on original)
// Verified on fix
// shouldn't hold in original but should probably hold in the fix.
rule zeroDepositZeroShares(uint assets, address receiver)
{
    env e;
    
    uint shares = deposit(e,assets, receiver);

    assert shares == 0 <=> assets == 0;
}

// also violated currently https://prover.certora.com/output/5771024/25e532c4e0894f6d8f3e8c1ac5ab49ec/
invariant assetsMoreThanSupply()
    totalAssets()  >= totalSupply() + fees() + lostAssets() //maybe need to change lostAssets() to the newLostAssets() in case it is not updated?
    {
        preserved with (env e) {
            require msgSender(e) != currentContract;
            address any;
            safeAssumptions(e, any , msgSender(e));
            // require lostAssets() == 0, "assuming no assets were lost";
            require lastTotalAssets() == realTotalAssets(), "no lost assets - phrased differently." ; 
            require fee() < wad(), "reasonable fee";
        }
    }

// Violated: https://prover.certora.com/output/5771024/b15799cc3bb74f438c991b341f2ee470/
// think about this.
// invariant assetsMoreThanSupply()
//     totalAssets() >= totalSupply()
//     {
//         preserved with (env e) {
//             require msgSender(e) != currentContract;
//             address any;
//             safeAssumptions(e, any , msgSender(e));
//         }
//     }

// Violated: https://prover.certora.com/output/5771024/b15799cc3bb74f438c991b341f2ee470/ // NOT RECHECKED
invariant noAssetsIfNoSupply() 
    // if EulerEarn has no assets then there are no shares - shouldn't hold
    // EulerEarn should have no assets 
    // the other one should hold - if no asset were sent to markets then no shares.
    // (Token0.balanceOf(currentContract) == 0 => totalSupply() == 0) &&
    (totalAssets() == 0 => (totalSupply() == 0)) {
        preserved with (env e) {
            address any;
            safeAssumptions(e, any, msgSender(e));
        }
    }

// Violated: https://prover.certora.com/output/5771024/b15799cc3bb74f438c991b341f2ee470/
invariant noSupplyIfNoAssets()
    ( Token0.balanceOf(currentContract) == 0 => totalSupply() == 0 ) &&
    ( totalAssets() == 0 <=> ( totalSupply() == 0 ))
    {
        preserved with (env e) {
            safeAssumptions(e, _, msgSender(e));
        }
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



////////////////////////////////////////////////////////////////////////////////
////                    #     State Transition                             /////
////////////////////////////////////////////////////////////////////////////////

// Violated: https://prover.certora.com/output/5771024/1c8ee641eeaa47bf8f7ecf1d92e1f145/
// should hold probably but 
rule totalsMonotonicity() {
    method f; env e; calldataarg args;
    require msgSender(e) != currentContract; 
    uint256 totalSupplyBefore = totalSupply();
    uint256 totalAssetsBefore = totalAssets();
    address receiver;
    safeAssumptions(e, receiver, msgSender(e));
    callReceiverFunctions(f, e, receiver);

    uint256 totalSupplyAfter = totalSupply();
    uint256 totalAssetsAfter = totalAssets();
    
    // possibly assert totalSupply and totalAssets must not change in opposite directions
    assert totalSupplyBefore < totalSupplyAfter  <=> totalAssetsBefore < totalAssetsAfter,
        "if totalSupply changes by a larger amount, the corresponding change in totalAssets must remain the same or grow";
    assert totalSupplyAfter == totalSupplyBefore => totalAssetsBefore == totalAssetsAfter,
        "equal size changes to totalSupply must yield equal size changes to totalAssets";
}

// Verified
rule underlyingCannotChange() {
    address originalAsset = asset();

    method f; env e; calldataarg args;
    f(e, args);

    address newAsset = asset();

    assert originalAsset == newAsset,
        "the underlying asset of a contract must not change";
}

////////////////////////////////////////////////////////////////////////////////
////                    #   High Level                                    /////
////////////////////////////////////////////////////////////////////////////////

// Violated : https://prover.certora.com/output/5771024/1c8ee641eeaa47bf8f7ecf1d92e1f145/
// should hold?
rule dustFavorsTheHouse(uint assetsIn )
{
    env e;
        
    require msgSender(e) != currentContract;
    safeAssumptions(e,msgSender(e),msgSender(e));
    uint256 totalSupplyBefore = totalSupply();

    uint balanceBefore = Token0.balanceOf(currentContract); //totalAssets() instead.

    uint shares = deposit(e,assetsIn, msgSender(e));
    uint assetsOut = redeem(e,shares,msgSender(e),msgSender(e));

    uint balanceAfter = Token0.balanceOf(currentContract);

    assert balanceAfter >= balanceBefore;
}

////////////////////////////////////////////////////////////////////////////////
////                       #   Risk Analysis                           /////////
////////////////////////////////////////////////////////////////////////////////

// Violated: https://prover.certora.com/output/5771024/a4623f525b0c4bae9a77ea0693ecaa6c/
// remove
// invariant vaultSolvency()
//     totalAssets() >= totalSupply()  && Token0.balanceOf(currentContract) >= totalAssets()  {
//       preserved with(env e){
//             requireInvariant zeroAllowanceOnAssets(msgSender(e));
//             requireInvariant totalSupplyIsSumOfBalances();
//             require msgSender(e) != currentContract;
//             require currentContract != asset(); 
//         }
//     }


// Violated: https://prover.certora.com/output/5771024/a4623f525b0c4bae9a77ea0693ecaa6c/
// not critical - maybe doesnt hold. maybe lower than 2?
rule redeemingAllValidity() { 
    address owner; 
    uint256 shares; require shares == balanceOf(owner);
    
    env e; safeAssumptions(e, _, owner);
    redeem(e, shares, _, owner);
    uint256 ownerBalanceAfter = balanceOf(owner);
    assert ownerBalanceAfter == 0;
}

// Violated: https://prover.certora.com/output/5771024/a4623f525b0c4bae9a77ea0693ecaa6c/
invariant zeroAllowanceOnAssets(address user)
    // if no allowance in assets then no allownace in shares.
    Token0.allowance(currentContract, user) == 0 && currentContract.allowance(currentContract, user) == 0 {
        preserved with(env e) {
            require msgSender(e) != currentContract;
        }
    }

////////////////////////////////////////////////////////////////////////////////
////               # stakeholder properties  (Risk Analysis )         //////////
////////////////////////////////////////////////////////////////////////////////

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

    safeAssumptions(e, contributor, receiver);

    uint256 contributorAssetsBefore = Token0.balanceOf(contributor); //in assets
    uint256 receiverSharesBefore = balanceOf(receiver); //in shares

    callContributionMethods(e, f, assets, shares, receiver);

    uint256 contributorAssetsAfter = Token0.balanceOf(contributor);
    uint256 receiverSharesAfter = balanceOf(receiver);

    assert contributorAssetsBefore > contributorAssetsAfter <=> receiverSharesBefore < receiverSharesAfter, //maybe leq or geq
        "a contributor's assets must decrease if and only if the receiver's shares increase";
}

// Verified
rule onlyContributionMethodsReduceAssets(method f) {
    address user; require user != currentContract;
    uint256 userBalanceOfBefore = Token0.balanceOf(user);

    env e; 
    calldataarg args;
    safeAssumptions(e, user, _);

    f(e, args);

    uint256 userBalanceOfAfter = Token0.balanceOf(user);

    assert userBalanceOfBefore > userBalanceOfAfter =>
        (f.selector == sig:deposit(uint256,address).selector ||
         f.selector == sig:mint(uint256,address).selector ||
         f.contract == asset() || f.contract == currentContract),
        "a user's assets must not go down except on calls to contribution methods or calls directly to the asset.";
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

    safeAssumptions(e, receiver, owner);

    uint256 ownerSharesBefore = balanceOf(owner);
    uint256 receiverAssetsBefore = Token0.balanceOf(receiver);

    callReclaimingMethods(e, f, assets, shares, receiver, owner);

    uint256 ownerSharesAfter = balanceOf(owner);
    uint256 receiverAssetsAfter = Token0.balanceOf(receiver);

    assert ownerSharesBefore > ownerSharesAfter <=> receiverAssetsBefore < receiverAssetsAfter,
        "an owner's shares must decrease if and only if the receiver's assets increase";
}



////////////////////////////////////////////////////////////////////////////////
////                        # helpers and miscellaneous                //////////
////////////////////////////////////////////////////////////////////////////////

function safeAssumptions(env e, address receiver, address owner) {
    require currentContract != asset(); // Although this is not disallowed, we assume the contract's underlying asset is not the contract itself
    requireInvariant totalSupplyIsSumOfBalances();
    // requireInvariant vaultSolvency();
    // requireInvariant noAssetsIfNoSupply();
    requireInvariant noSupplyIfNoAssets();
    requireInvariant assetsMoreThanSupply();

    require msgSender(e) != currentContract;  // This is proved by rule noDynamicCalls
    requireInvariant zeroAllowanceOnAssets(msgSender(e));

    require ( (receiver != owner => balanceOf(owner) + balanceOf(receiver) <= totalSupply())  && 
                balanceOf(receiver) <= totalSupply() &&
                balanceOf(owner) <= totalSupply());
}


// A helper function to set the receiver 
function callReceiverFunctions(method f, env e, address receiver) {
    uint256 amount;
    if (f.selector == sig:deposit(uint256,address).selector) {
        deposit(e, amount, receiver);
    } else if (f.selector == sig:mint(uint256,address).selector) {
        mint(e, amount, receiver);
    } else if (f.selector == sig:withdraw(uint256,address,address).selector) {
        address owner;
        withdraw(e, amount, receiver, owner);
    } else if (f.selector == sig:redeem(uint256,address,address).selector) {
        address owner;
        redeem(e, amount, receiver, owner);
    } else {
        calldataarg args;
        f(e, args);
    }
}


function callContributionMethods(env e, method f, uint256 assets, uint256 shares, address receiver) {
    if (f.selector == sig:deposit(uint256,address).selector) {
        deposit(e, assets, receiver);
    }
    if (f.selector == sig:mint(uint256,address).selector) {
        mint(e, shares, receiver);
    }
}

function callReclaimingMethods(env e, method f, uint256 assets, uint256 shares, address receiver, address owner) {
    if (f.selector == sig:withdraw(uint256,address,address).selector) {
        withdraw(e, assets, receiver, owner);
    }
    if (f.selector == sig:redeem(uint256,address,address).selector) {
        redeem(e, shares, receiver, owner);
    }
}

function callFunctionsWithReceiverAndOwner(env e, method f, uint256 assets, uint256 shares, address receiver, address owner) {
    if (f.selector == sig:withdraw(uint256,address,address).selector) {
        withdraw(e, assets, receiver, owner);
    }
    else if (f.selector == sig:redeem(uint256,address,address).selector) {
        redeem(e, shares, receiver, owner);
    } 
    else if (f.selector == sig:deposit(uint256,address).selector) {
        deposit(e, assets, receiver);
    }
    else if (f.selector == sig:mint(uint256,address).selector) {
        mint(e, shares, receiver);
    }
    else if (f.selector == sig:transferFrom(address,address,uint256).selector) {
        transferFrom(e, owner, receiver, shares);
    }
    else {
        calldataarg args;
        f(e, args);
    }
}