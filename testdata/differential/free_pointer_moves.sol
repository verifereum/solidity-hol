// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.0;

// The free memory pointer before and after one operation.
contract FreePointerMoves {
    struct Named {
        uint256 id;
        string name;
    }

    event E(string a);
    event I(string indexed a);
    error Err(string a);

    string constant C = "abc";
    string s;
    bytes b;
    mapping(string => uint256) m;
    Named st0;
    Named st;
    string s2;

    function init() internal {
        assembly {
            sstore(s.slot, 0x6162630000000000000000000000000000000000000000000000000000000006)
            sstore(b.slot, 0x0102000000000000000000000000000000000000000000000000000000000004)
            sstore(st0.slot, 5)
            sstore(add(st0.slot, 1), 0x6162630000000000000000000000000000000000000000000000000000000006)
        }
    }

    function len(string memory x) internal pure returns (uint256) {
        return bytes(x).length;
    }

    function extLen(string calldata x) external pure returns (uint256) {
        return bytes(x).length;
    }

    function extStr() external pure returns (string memory) {
        return "abc";
    }

    function hashLit() external returns (uint256 p0, uint256 p1) {
        init();
        assembly {
            p0 := mload(0x40)
        }
        bytes32 h = keccak256("abc"); h;
        assembly {
            p1 := mload(0x40)
        }
    }

    function hashStorage() external returns (uint256 p0, uint256 p1) {
        init();
        assembly {
            p0 := mload(0x40)
        }
        bytes32 h = keccak256(b); h;
        assembly {
            p1 := mload(0x40)
        }
    }

    function hashString() external returns (uint256 p0, uint256 p1) {
        init();
        assembly {
            p0 := mload(0x40)
        }
        bytes32 h = keccak256(bytes(s)); h;
        assembly {
            p1 := mload(0x40)
        }
    }

    function hashCalldata(bytes calldata d) external returns (uint256 p0, uint256 p1) {
        init();
        assembly {
            p0 := mload(0x40)
        }
        bytes32 h = keccak256(d); h;
        assembly {
            p1 := mload(0x40)
        }
    }

    function shaLit() external returns (uint256 p0, uint256 p1) {
        init();
        assembly {
            p0 := mload(0x40)
        }
        bytes32 h = sha256("abc"); h;
        assembly {
            p1 := mload(0x40)
        }
    }

    function shaStorage() external returns (uint256 p0, uint256 p1) {
        init();
        assembly {
            p0 := mload(0x40)
        }
        bytes32 h = sha256(b); h;
        assembly {
            p1 := mload(0x40)
        }
    }

    function emitLit() external returns (uint256 p0, uint256 p1) {
        init();
        assembly {
            p0 := mload(0x40)
        }
        emit E("abc");
        assembly {
            p1 := mload(0x40)
        }
    }

    function emitIndexedLit() external returns (uint256 p0, uint256 p1) {
        init();
        assembly {
            p0 := mload(0x40)
        }
        emit I("abc");
        assembly {
            p1 := mload(0x40)
        }
    }

    function emitStorage() external returns (uint256 p0, uint256 p1) {
        init();
        assembly {
            p0 := mload(0x40)
        }
        emit E(s);
        assembly {
            p1 := mload(0x40)
        }
    }

    function emitIndexedStorage() external returns (uint256 p0, uint256 p1) {
        init();
        assembly {
            p0 := mload(0x40)
        }
        emit I(s);
        assembly {
            p1 := mload(0x40)
        }
    }

    function emitConst() external returns (uint256 p0, uint256 p1) {
        init();
        assembly {
            p0 := mload(0x40)
        }
        emit E(C);
        assembly {
            p1 := mload(0x40)
        }
    }

    function memLit() external returns (uint256 p0, uint256 p1) {
        init();
        assembly {
            p0 := mload(0x40)
        }
        string memory x = "abc"; x;
        assembly {
            p1 := mload(0x40)
        }
    }

    function constMem() external returns (uint256 p0, uint256 p1) {
        init();
        assembly {
            p0 := mload(0x40)
        }
        string memory x = C; x;
        assembly {
            p1 := mload(0x40)
        }
    }

    function constAssign() external returns (uint256 p0, uint256 p1) {
        init();
        assembly {
            p0 := mload(0x40)
        }
        s2 = C;
        assembly {
            p1 := mload(0x40)
        }
    }

    function mapLit() external returns (uint256 p0, uint256 p1) {
        init();
        assembly {
            p0 := mload(0x40)
        }
        uint256 v = m["abc"]; v;
        assembly {
            p1 := mload(0x40)
        }
    }

    function mapStorageKey() external returns (uint256 p0, uint256 p1) {
        init();
        assembly {
            p0 := mload(0x40)
        }
        uint256 v = m[s]; v;
        assembly {
            p1 := mload(0x40)
        }
    }

    function mapConstKey() external returns (uint256 p0, uint256 p1) {
        init();
        assembly {
            p0 := mload(0x40)
        }
        uint256 v = m[C]; v;
        assembly {
            p1 := mload(0x40)
        }
    }

    function mapCalldataKey(string calldata k) external returns (uint256 p0, uint256 p1) {
        init();
        assembly {
            p0 := mload(0x40)
        }
        uint256 v = m[k]; v;
        assembly {
            p1 := mload(0x40)
        }
    }

    function mapWriteLit() external returns (uint256 p0, uint256 p1) {
        init();
        assembly {
            p0 := mload(0x40)
        }
        m["abc"] = 7;
        assembly {
            p1 := mload(0x40)
        }
    }

    function structCtor() external returns (uint256 p0, uint256 p1) {
        init();
        assembly {
            p0 := mload(0x40)
        }
        st = Named(1, "abc");
        assembly {
            p1 := mload(0x40)
        }
    }

    function structMem() external returns (uint256 p0, uint256 p1) {
        init();
        assembly {
            p0 := mload(0x40)
        }
        Named memory n = Named(1, "abc"); n;
        assembly {
            p1 := mload(0x40)
        }
    }

    function structRead() external returns (uint256 p0, uint256 p1) {
        init();
        assembly {
            p0 := mload(0x40)
        }
        string memory x = st0.name; x;
        assembly {
            p1 := mload(0x40)
        }
    }

    function structToMem() external returns (uint256 p0, uint256 p1) {
        init();
        assembly {
            p0 := mload(0x40)
        }
        Named memory n = st0; n;
        assembly {
            p1 := mload(0x40)
        }
    }

    function structToStorage() external returns (uint256 p0, uint256 p1) {
        init();
        assembly {
            p0 := mload(0x40)
        }
        st = st0;
        assembly {
            p1 := mload(0x40)
        }
    }

    function internalArg() external returns (uint256 p0, uint256 p1) {
        init();
        assembly {
            p0 := mload(0x40)
        }
        uint256 v = len("abc"); v;
        assembly {
            p1 := mload(0x40)
        }
    }

    function internalStorageArg() external returns (uint256 p0, uint256 p1) {
        init();
        assembly {
            p0 := mload(0x40)
        }
        uint256 v = len(s); v;
        assembly {
            p1 := mload(0x40)
        }
    }

    function concatLit() external returns (uint256 p0, uint256 p1) {
        init();
        assembly {
            p0 := mload(0x40)
        }
        bytes memory x = bytes.concat("a", b); x;
        assembly {
            p1 := mload(0x40)
        }
    }

    function stringConcat() external returns (uint256 p0, uint256 p1) {
        init();
        assembly {
            p0 := mload(0x40)
        }
        string memory x = string.concat(s, "x"); x;
        assembly {
            p1 := mload(0x40)
        }
    }

    function encodeLit() external returns (uint256 p0, uint256 p1) {
        init();
        assembly {
            p0 := mload(0x40)
        }
        bytes memory x = abi.encode("abc"); x;
        assembly {
            p1 := mload(0x40)
        }
    }

    function encodeStorage() external returns (uint256 p0, uint256 p1) {
        init();
        assembly {
            p0 := mload(0x40)
        }
        bytes memory x = abi.encode(s, b); x;
        assembly {
            p1 := mload(0x40)
        }
    }

    function packedLit() external returns (uint256 p0, uint256 p1) {
        init();
        assembly {
            p0 := mload(0x40)
        }
        bytes memory x = abi.encodePacked("abc", uint8(1)); x;
        assembly {
            p1 := mload(0x40)
        }
    }

    function packedStorage() external returns (uint256 p0, uint256 p1) {
        init();
        assembly {
            p0 := mload(0x40)
        }
        bytes memory x = abi.encodePacked(s, b); x;
        assembly {
            p1 := mload(0x40)
        }
    }

    function compare() external returns (uint256 p0, uint256 p1) {
        init();
        assembly {
            p0 := mload(0x40)
        }
        bool e = keccak256(bytes(s)) == keccak256("abc"); e;
        assembly {
            p1 := mload(0x40)
        }
    }

    function storageToStorage() external returns (uint256 p0, uint256 p1) {
        init();
        assembly {
            p0 := mload(0x40)
        }
        s2 = s;
        assembly {
            p1 := mload(0x40)
        }
    }

    function ternaryLit(bool c) external returns (uint256 p0, uint256 p1) {
        init();
        assembly {
            p0 := mload(0x40)
        }
        string memory x = c ? "a" : "bb"; x;
        assembly {
            p1 := mload(0x40)
        }
    }

    function fixedLit() external returns (uint256 p0, uint256 p1) {
        init();
        assembly {
            p0 := mload(0x40)
        }
        bytes32 x = "abc"; x;
        assembly {
            p1 := mload(0x40)
        }
    }

    function bytesToString() external returns (uint256 p0, uint256 p1) {
        init();
        assembly {
            p0 := mload(0x40)
        }
        string memory x = string(b); x;
        assembly {
            p1 := mload(0x40)
        }
    }

    function stringToBytes() external returns (uint256 p0, uint256 p1) {
        init();
        assembly {
            p0 := mload(0x40)
        }
        bytes memory x = bytes(s); x;
        assembly {
            p1 := mload(0x40)
        }
    }

    function storageConv() external returns (uint256 p0, uint256 p1) {
        init();
        assembly {
            p0 := mload(0x40)
        }
        s2 = string(b);
        assembly {
            p1 := mload(0x40)
        }
    }

    function newArray() external returns (uint256 p0, uint256 p1) {
        init();
        assembly {
            p0 := mload(0x40)
        }
        uint256[] memory a = new uint256[](3); a;
        assembly {
            p1 := mload(0x40)
        }
    }

    function newBytes() external returns (uint256 p0, uint256 p1) {
        init();
        assembly {
            p0 := mload(0x40)
        }
        bytes memory a = new bytes(5); a;
        assembly {
            p1 := mload(0x40)
        }
    }

    function arrayLit() external returns (uint256 p0, uint256 p1) {
        init();
        assembly {
            p0 := mload(0x40)
        }
        uint256[3] memory a = [uint256(1), 2, 3]; a;
        assembly {
            p1 := mload(0x40)
        }
    }

    function extLitArg() external returns (uint256 p0, uint256 p1) {
        init();
        assembly {
            p0 := mload(0x40)
        }
        uint256 v = this.extLen("abc"); v;
        assembly {
            p1 := mload(0x40)
        }
    }

    function extStorageArg() external returns (uint256 p0, uint256 p1) {
        init();
        assembly {
            p0 := mload(0x40)
        }
        uint256 v = this.extLen(s); v;
        assembly {
            p1 := mload(0x40)
        }
    }

    function extRet() external returns (uint256 p0, uint256 p1) {
        init();
        assembly {
            p0 := mload(0x40)
        }
        string memory x = this.extStr(); x;
        assembly {
            p1 := mload(0x40)
        }
    }

    function requireLit() external returns (uint256 p0, uint256 p1) {
        init();
        assembly {
            p0 := mload(0x40)
        }
        require(b.length == 2, "abc");
        assembly {
            p1 := mload(0x40)
        }
    }

    function decodeCalldata(bytes calldata d) external returns (uint256 p0, uint256 p1) {
        init();
        assembly {
            p0 := mload(0x40)
        }
        string memory x = abi.decode(d, (string)); x;
        assembly {
            p1 := mload(0x40)
        }
    }

    function pushByte() external returns (uint256 p0, uint256 p1) {
        init();
        assembly {
            p0 := mload(0x40)
        }
        b.push(0x03);
        assembly {
            p1 := mload(0x40)
        }
    }

    function deleteString() external returns (uint256 p0, uint256 p1) {
        init();
        assembly {
            p0 := mload(0x40)
        }
        delete s;
        assembly {
            p1 := mload(0x40)
        }
    }

    function lengthRead() external returns (uint256 p0, uint256 p1) {
        init();
        assembly {
            p0 := mload(0x40)
        }
        uint256 v = bytes(s).length + b.length; v;
        assembly {
            p1 := mload(0x40)
        }
    }

    function indexRead() external returns (uint256 p0, uint256 p1) {
        init();
        assembly {
            p0 := mload(0x40)
        }
        bytes1 v = b[1]; v;
        assembly {
            p1 := mload(0x40)
        }
    }

    function selectorLit() external returns (uint256 p0, uint256 p1) {
        init();
        assembly {
            p0 := mload(0x40)
        }
        bytes memory x = abi.encodeWithSignature("f(uint256)", 1); x;
        assembly {
            p1 := mload(0x40)
        }
    }

    function encodeCall() external returns (uint256 p0, uint256 p1) {
        init();
        assembly {
            p0 := mload(0x40)
        }
        bytes memory x = abi.encodeCall(this.extLen, ("abc")); x;
        assembly {
            p1 := mload(0x40)
        }
    }

    function errorSelector() external returns (uint256 p0, uint256 p1) {
        init();
        assembly {
            p0 := mload(0x40)
        }
        bytes4 x = Err.selector; x;
        assembly {
            p1 := mload(0x40)
        }
    }
}
