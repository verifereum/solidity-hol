// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

// abi.encodeWithSignature of a signature computed at run time, and
// abi.encodePacked of arrays of static arrays. A signature that is not a
// literal is hashed after the arguments are evaluated: a calldata or storage
// one is first copied to memory, and that copy is freed again before the
// encoding is allocated, so the encoding lands where the copy was and the
// copy's bytes past the encoding's end stay in memory. The dump functions
// return memory from 0 to 256 bytes past the free memory pointer.
contract AbiSignatures {
    struct Named {
        uint256 a;
        string name;
    }

    string constant SIG = "transfer(address,uint256)";
    string stored;
    uint8[2][] packedStored;

    function literal(uint256 x) external pure returns (bytes memory) {
        return abi.encodeWithSignature("f(uint256)", x);
    }

    function fromMemory(string memory s, uint256 x) external pure returns (bytes memory) {
        return abi.encodeWithSignature(s, x);
    }

    function fromCalldata(string calldata s, bytes calldata b) external pure returns (bytes memory) {
        return abi.encodeWithSignature(s, b);
    }

    function fromStorage(string memory s, uint256 x) external returns (bytes memory) {
        stored = s;
        return abi.encodeWithSignature(stored, x);
    }

    function fromConstant(address to, uint256 x) external pure returns (bytes memory) {
        return abi.encodeWithSignature(SIG, to, x);
    }

    function fromField(string memory s) external pure returns (bytes memory) {
        Named memory n = Named(7, s);
        return abi.encodeWithSignature(n.name, n.a, n);
    }

    // The arguments are evaluated before the signature is read.
    function evaluationOrder() external returns (bytes memory) {
        stored = "a()";
        return abi.encodeWithSignature(stored, setStored("b()"));
    }

    function setStored(string memory s) internal returns (uint256) {
        stored = s;
        return 1;
    }

    // The freed copy is reused by the next allocation, which clears it.
    function reused(string calldata s) external pure returns (bytes memory r, uint256[] memory a) {
        r = abi.encodeWithSignature(s);
        a = new uint256[](3);
    }

    function dumpCalldata(string calldata s) external pure {
        bytes memory r = abi.encodeWithSignature(s);
        assembly { mstore(add(mload(0x40), 0xe0), r) return(0, add(mload(0x40), 0x100)) }
    }

    function dumpStorage(string memory s) external {
        stored = s;
        bytes memory r = abi.encodeWithSignature(stored);
        assembly { mstore(add(mload(0x40), 0xe0), r) return(0, add(mload(0x40), 0x100)) }
    }

    function dumpMemory(string memory s, uint256 x) external pure {
        bytes memory r = abi.encodeWithSignature(s, x);
        assembly { mstore(add(mload(0x40), 0xe0), r) return(0, add(mload(0x40), 0x100)) }
    }

    // Freeing the copy checks the free memory pointer, as an allocation does.
    function freedPastLimit(string memory s) external pure returns (bytes memory) {
        assembly { mstore(0x40, shl(64, 1)) }
        return abi.encodeWithSignature(s);
    }

    function packedMemory(uint256[2][] memory a, uint8[2][3] memory b) external pure returns (bytes memory) {
        return abi.encodePacked(a, b);
    }

    function packedDeep(bytes3[2][2][] memory a, int16 x) external pure returns (bytes memory) {
        return abi.encodePacked(x, a, x);
    }

    function packedCalldata(uint16[2][] calldata a, bool[3][1] calldata b) external pure returns (bytes memory) {
        return abi.encodePacked(a, b);
    }

    function packedStorage(uint8[2][] memory a) external returns (bytes memory) {
        packedStored = a;
        return abi.encodePacked(packedStored);
    }

    function packedHash(uint32[2][2] memory a) external pure returns (bytes32) {
        return keccak256(abi.encodePacked(a));
    }
}
