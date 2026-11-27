// SPDX-License-Identifier: GPL-3.0
pragma solidity >=0.8.0;

contract ExternalFunctionLimits {
    function(uint256) internal pure returns (uint256) stored;

    function readsStored(uint256 x) public view returns (uint256) {
        return stored(x);
    }

    function callsExternal(function(uint256) external view returns (uint256) g)
        external view returns (uint256)
    {
        return g(1);
    }

    function catchesExternal(function(uint256) external view returns (uint256) g)
        external view returns (uint256)
    {
        try g(1) returns (uint256 x) {
            return x;
        } catch {
            return 0;
        }
    }
}
