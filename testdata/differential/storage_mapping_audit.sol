// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;
contract StorageMappingAudit {
    bytes b;
    mapping(uint256 => uint256) m;
    mapping(uint256 => uint256)[] a;
    mapping(uint256 => uint256)[2] s;

    function deleteMapArr() external returns (uint256 scratch0) {
        a.push();
        a[0][7] = 1;
        m[7] = 1;
        delete a;
        assembly { scratch0 := mload(0) }
    }

    function popMapArr() external returns (uint256 scratch0) {
        a.push();
        a[0][7] = 1;
        m[7] = 1;
        a.pop();
        assembly { scratch0 := mload(0) }
    }

    function deleteStaticMapArr() external returns (uint256 scratch0) {
        s[0][7] = 1;
        delete s;
        assembly { scratch0 := mload(0) }
    }
}
