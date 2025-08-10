import "./EulerEarnERC4626.spec";

methods {
    // function EulerEarn.HOOK_after_withdrawStrategy(uint256 assets) internal => CVL_after_withdrawStrategy(assets);
    // function _._decimalsOffset() internal => 0 expect uint8;
    function EulerEarn.HOOK_after_accrueInterest() internal => CVL_after_accrueInterest();
}

ghost uint256 totalSupplyGhost;
ghost uint256 assetsInGhost;
ghost uint256 totalAssetsAfterWithdrawStrategy;

// The three properties are solvency properties on the internal parts of the extenral deposit,withdraw,mint,redeem:

// Verified https://prover.certora.com/output/5771024/455e0433202940aebcd4aa94b939561e/
rule propertiesAfterAccrue() {
    require totalAssets() >= totalSupply() + fees();
    env e;
    _accrueInterest(e);
    assert fees() == 0; 
    assert totalAssets() >= totalSupply() + fees();
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
    // requireInvariant feeInRange();
    // requireInvariant noAssetsOnEuler();
    // requireInvariant configBalanceAndTotalSupply(withdrawQueueFirstVault);   

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
    assert require_uint256(require_uint256(totalAssetsPost-feeAssets)+virtualAmount()) >= require_uint256(totalSupplyPost+virtualAmount());
    assert feesPost <= feeAssets;
    assert feesPost <= totalInterest;
    assert totalAssetsPost >= totalSupplyPost + feesPost, "solvent after"; // verified if we assume feesPost <= totalInterest 
}



// Hook summaries that serve as lemmas for the solvencyInInternalWithdraw rule 
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

// Verified https://prover.certora.com/output/5771024/455e0433202940aebcd4aa94b939561e/
rule solvencyInInternalDeposit() {
    // simulating the internal _deposit in a call from the external deposit
    env e;
    address caller;
    address receiver;
    uint256 assets;
    uint256 shares;
    safeAssumptions(e);

    uint256 totalAssetsPre; 
    uint256 feesPre;
    uint256 lostAssetsPre;
    uint256 totalSupplyPre = totalSupply();
    (feesPre,totalAssetsPre,lostAssetsPre) =  _accruedFeeAndAssets(e);
    
    uint256 lastTotalAssetsPre = lastTotalAssets();
    require totalAssetsPre >= totalSupplyPre + feesPre, "solvent before";
    require lastTotalAssetsPre == totalAssetsPre, "_deposit is called after _accrueInterest";
    
    require shares == _convertToSharesWithTotals(e,assets, totalSupplyPre, lastTotalAssetsPre, Math.Rounding.Floor);

    _deposit(e,caller,receiver,assets,shares);

    uint256 totalAssetsPost; 
    uint256 feesPost;
    uint256 lostAssetsPost;
    uint256 totalSupplyPost = totalSupply();
    (feesPost,totalAssetsPost,lostAssetsPost) =  _accruedFeeAndAssets(e);

    assert totalAssetsPost >= totalSupplyPost + feesPost, "solvent after";
}


// this doesn't make sense?
rule solvencyEnablesWithdraw() {
    // interesting revert condition we need to consider - if the vault doesn't have enough assets then _withdrawStategy reverts
    // so we also need the vault to be solvent, currently we didn't assume this.

    env e;
    safeAssumptions(e);
    uint256 assets;
    address receiver;
    address owner;
    bool reentrancyEntered = reentrancyGuardEntered();
    require !reentrancyEntered;

    address evcOwner = EVC.getAccountOwner(receiver);
    require evcOwner == 0 || evcOwner == receiver;

    require assets <= 2^128;

    require assets <= maxWithdraw(e,owner);
    address msgSender = msgSender(e);
    require msgSender != 0;
    require owner != 0;
    require receiver != 0;
    uint256 totalAssetsPre; 
    uint256 feesPre;
    uint256 lostAssetsPre;
    uint256 totalSupplyPre = totalSupply();
    (feesPre,totalAssetsPre,lostAssetsPre) =  _accruedFeeAndAssets(e); // 6 non-linear ops 
    uint256 lastTotalAssetsPre = lastTotalAssets();
    require totalAssetsPre >= totalSupplyPre + feesPre, "solvent before";

    uint256 shares = _convertToSharesWithTotals(e,assets, totalSupplyPre, lastTotalAssetsPre, Math.Rounding.Ceil);

    uint256 currentAllowance = allowance(owner, msgSender); //the allowance in EulerEarn shares
    require currentAllowance >= shares, "allowance needs to suffice for withdraw";
  


    withdraw@withrevert(e,assets,receiver,owner);
    bool reverted = lastReverted;

    uint256 totalAssetsPost; 
    uint256 feesPost;
    uint256 lostAssetsPost;
    uint256 totalSupplyPost = totalSupply();
    (feesPost,totalAssetsPost,lostAssetsPost) =  _accruedFeeAndAssets(e); // 6 non-linear ops 
    uint256 lastTotalAssetsPost = lastTotalAssets(); 
    
    assert !reverted;
}

// this doesn't make sense?
rule solvencyEnablesInternalWithdraw() {
    
    env e;
    safeAssumptions(e); // 7 non-linear ops
    uint256 shares;
    uint256 assets;
    address receiver;
    address owner;
    address caller;
    bool reentrancyEntered = reentrancyGuardEntered();
    require !reentrancyEntered;

    address evcOwner = EVC.getAccountOwner(receiver);
    require evcOwner == 0 || evcOwner == receiver;

    require assets <= 2^128;

    // require assets <= maxWithdraw(e,owner); // 17 non-linear ops -- expensive
    require withdrawQueueLength() == 1; 
    address withdrawQueueFirstVault = withdrawQGetAt(0);
    require assets <= withdrawQueueFirstVault.maxWithdraw(e,currentContract); // not sure!

    address msgSender = msgSender(e);
    require msgSender != 0;
    require owner != 0;
    require receiver != 0;
    require caller == msgSender;

    
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

    bool assetSharesRelationInWithdraw = ( shares == _convertToSharesWithTotals(e,assets, totalSupplyPre, lastTotalAssetsPre, Math.Rounding.Ceil) ); // 2 non-linear ops
    bool assetSharesRelationInRedeem = ( assets == _convertToAssetsWithTotals(e,shares, totalSupplyPre, lastTotalAssetsPre, Math.Rounding.Floor)); // 2 non-linear ops
    require assetSharesRelationInWithdraw || assetSharesRelationInRedeem,
        "internal withdraw is called either in the external withdraw or the external redeem";

    uint256 currentAllowance = allowance(owner, msgSender); //the allowance in EulerEarn shares
    require currentAllowance >= shares, "allowance needs to suffice for withdraw";
  


    _withdraw@withrevert(e,caller,receiver,owner,assets,shares); // 22 non-linear ops -> cvlDispatchMaxWithdraw - 4, cvlDispatchPreviewRedeem - 4, CVL_after_withdrawStrategy - 6 
    bool reverted = lastReverted;

    assert !reverted;

}


rule withdrawFrontRun(method f) 
filtered {
    f -> !f.isView
}
{
    calldataarg args;
    env e1;
    env e2;
    safeAssumptions(e1);
    require e1.msg.sender != e2.msg.sender;
    require e1.msg.sender != currentContract;
    require e2.msg.sender != currentContract;
    storage start = lastStorage;

    uint256 assets;
    address receiver;
    address owner;

    withdraw@withrevert(e1,assets,receiver,owner);
    bool reverted1 = lastReverted;

    f(e2, args) at start;
    withdraw@withrevert(e1,assets,receiver,owner);
    bool reverted2 = lastReverted;

    assert reverted2 => reverted1;
}