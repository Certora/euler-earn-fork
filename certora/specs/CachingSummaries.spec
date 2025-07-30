methods {
    function _._accruedFeeAndAssets() internal with (env e) => _accruedFeeAndAssetsWithCaching(e) expect (uint256,uint256,uint256); // If this summary is used you need to call initCacheToZero at the start of every rule/invariant
}

//summarization with caching -- doesn't approximate anything -- sometimes easier for the prover

ghost uint256 lastTotalAssetsCached;
ghost uint256 lostAssetsCached;
ghost uint96 feeCached;
ghost uint256 totalSupplyCached;
ghost address firstMarketCached;
ghost uint256 firstMarketExpectedSupplyAssetsCached;
ghost uint256 feeSharesCached; 
ghost uint256 newTotalAssetsCached;
ghost uint256 newLostAssetsCached;

function initCacheToZero() {
    feeSharesCached = 0;
    newTotalAssetsCached = 0;
    newLostAssetsCached = 0;
}
function _accruedFeeAndAssetsWithCaching(env e) returns (uint256,uint256,uint256) {
    uint256 lastTotalAssets = lastTotalAssets();
    uint256 lostAssets = lostAssets();
    uint96 fee = fee();
    uint256 totalSupply = totalSupply();
    address firstMarket = withdrawQGetAt(0);
    uint256 firstMarketExpectedSupplyAssets = expectedSupplyAssets(firstMarket);
    if (feeSharesCached == 0 && newTotalAssetsCached == 0 && newLostAssetsCached == 0) {
        lastTotalAssetsCached = lastTotalAssets;
        lostAssetsCached = lostAssets;
        feeCached = fee;
        totalSupplyCached = totalSupply;
        firstMarketCached = firstMarket;
        firstMarketExpectedSupplyAssetsCached = firstMarketExpectedSupplyAssets; 
        uint256 feeSharesRet;
        uint256 newTotalAssetsRet;
        uint256 newLostAssetsRet;
        (feeSharesRet, newTotalAssetsRet, newLostAssetsRet) = accruedFeeAndAssetsNotSummarized(e);
        feeSharesCached = feeSharesRet;
        newTotalAssetsCached = newTotalAssetsRet;
        newLostAssetsCached = newLostAssetsRet;
        return (feeSharesRet, newTotalAssetsRet, newLostAssetsRet);
    }
    else {
        if (
            lastTotalAssets == lastTotalAssetsCached &&
            lostAssets == lostAssetsCached &&
            fee == feeCached && 
            totalSupply == totalSupplyCached && 
            firstMarket == firstMarketCached &&
            firstMarketExpectedSupplyAssets == firstMarketExpectedSupplyAssetsCached 
        ) {
            uint256 feeSharesRet = feeSharesCached;
            uint256 newTotalAssetsRet = newTotalAssetsCached;
            uint256 newLostAssetsRet = newLostAssetsCached;
            return (feeSharesRet,newTotalAssetsRet,newLostAssetsRet);
        }
        else {
            lastTotalAssetsCached = lastTotalAssets;
            lostAssetsCached = lostAssets;
            feeCached = fee;
            totalSupplyCached = totalSupply;
            firstMarketCached = firstMarket;
            firstMarketExpectedSupplyAssetsCached = firstMarketExpectedSupplyAssets; 
            uint256 feeSharesRet;
            uint256 newTotalAssetsRet;
            uint256 newLostAssetsRet;
            (feeSharesRet, newTotalAssetsRet, newLostAssetsRet) = accruedFeeAndAssetsNotSummarized(e);
            feeSharesCached = feeSharesRet;
            newTotalAssetsCached = newTotalAssetsRet;
            newLostAssetsCached = newLostAssetsRet;
            return (feeSharesRet, newTotalAssetsRet, newLostAssetsRet);
        }
    }
}