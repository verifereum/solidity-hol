// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

// What memory each compiled encoder leaves when reading one of its inputs
// ends the frame: it writes its output in place and reads each input only
// when it reaches it, so everything before the failing input is written.

enum E { A, B }

struct Pair { uint256 a; E e; }

struct Mixed { uint256 a; E e; string s; }

struct Holder { uint256 a; string s; }

struct Stored { uint256 k; string s; }

struct Three { string e; uint256 k; string bad; }

interface IPeer {
    function take(Pair[] calldata xs) external returns (uint256);
}

contract Child {
    uint256 public n;

    constructor(Pair[] memory xs) {
        n = xs.length;
    }
}

contract PartialEncodings {
    string text;
    string data;
    Stored st;
    Three th;

    error Dynamic(string a, string b, uint256 k);

    event Data(uint256 indexed k, Mixed m);
    event Indexed(Mixed indexed m);
    event Text(string s);
    event StoredThree(Three indexed t);

    // Pairs [(1, A), (2, 7)]: the second's enum word is out of range.
    function badPairs() internal pure returns (Pair[] memory xs) {
        xs = new Pair[](2);
        xs[0] = Pair(1, E.A);
        xs[1].a = 2;
        Pair memory p = xs[1];
        assembly { mstore(add(p, 32), 7) }
    }

    function badMixed() internal pure returns (Mixed memory m) {
        m.a = 3;
        m.s = "tail";
        assembly { mstore(add(m, 32), 9) }
    }

    function badEnums() internal pure returns (E[] memory es) {
        es = new E[](3);
        es[1] = E.B;
        assembly { mstore(add(es, 96), 4) }
    }

    // text is read whole, data's header is malformed.
    function errorStorageHeader() external view {
        revert Dynamic(text, data, 7);
    }

    function returnEnum() external pure returns (string memory, E[] memory) {
        return ("head", badEnums());
    }

    function encodeCalldata(Pair[] calldata xs) external pure returns (bytes memory) {
        return abi.encode(uint256(9), xs);
    }

    function encodeCalldataField(Holder calldata h) external pure returns (bytes memory) {
        return abi.encode(h);
    }

    function encodeSelector() external pure returns (bytes memory) {
        return abi.encodeWithSelector(0x12345678, "ab", badEnums());
    }

    function encodeStorageField() external view returns (bytes memory) {
        return abi.encode(st);
    }

    function encodePacked() external pure returns (bytes memory) {
        return abi.encodePacked(uint16(0x0102), badEnums());
    }

    function callPrefix() external returns (uint256) {
        return IPeer(address(0x1234)).take(badPairs());
    }

    function createPrefix() external returns (address) {
        return address(new Child(badPairs()));
    }

    function emitData() external {
        emit Data(5, badMixed());
    }

    function emitIndexed() external {
        emit Indexed(badMixed());
    }

    function emitStorageHeader() external {
        emit Text(data);
    }

    // th.e is empty, its slot dirty past the length byte; th.bad's header
    // is malformed. The empty string's spill is overwritten by th.k.
    function emitStoredSpill() external {
        emit StoredThree(th);
    }
}
