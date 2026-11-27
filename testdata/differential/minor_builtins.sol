// SPDX-License-Identifier: GPL-3.0
pragma solidity 0.8.37;

contract MinorBuiltins {
    function leadingZeros(uint256 x) external pure returns (uint256 r) {
        assembly { r := clz(x) }
    }

    function blobHash(uint256 i) external view returns (bytes32) {
        return blobhash(i);
    }

    function assemblyBlobHash(uint256 i) external view returns (bytes32 r) {
        assembly { r := blobhash(i) }
    }

    function blobBaseFee() external view returns (uint256) {
        return block.blobbasefee;
    }

    function assemblyBlobBaseFee() external view returns (uint256 r) {
        assembly { r := blobbasefee() }
    }

    function digest(bytes calldata data)
        external pure returns (bytes20 hash, bytes32 scratch, uint256 returnSize, bytes32 returnWord)
    {
        hash = ripemd160(data);
        assembly {
            scratch := mload(0)
            returnSize := returndatasize()
            returndatacopy(32, 0, 32)
            returnWord := mload(32)
        }
    }

    function namespaceSlot(string calldata id) external pure returns (uint256 slot, bytes32 scratch) {
        slot = erc7201(id);
        assembly { scratch := mload(0) }
    }

    function literalSlot() external pure returns (uint256 slot, uint256 scratch) {
        assembly { mstore(0, 0x2a) }
        slot = erc7201("example.namespace");
        assembly { scratch := mload(0) }
    }
}
