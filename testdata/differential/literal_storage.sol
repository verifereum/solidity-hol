// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.0;

// The free memory pointer before and after a string or hex literal is
// written to storage.
contract LiteralStorage {
    struct Named {
        uint256 id;
        string name;
    }

    string s;
    bytes b;
    string[] ss;
    Named st;
    uint256 x;
    string init = "abc";
    uint256 public atConstruction;

    constructor() {
        uint256 p;
        assembly {
            p := mload(0x40)
        }
        atConstruction = p;
    }

    function assign() external returns (uint256 p0, uint256 p1) {
        assembly {
            p0 := mload(0x40)
        }
        s = "abc";
        assembly {
            p1 := mload(0x40)
        }
    }

    function assignLong() external returns (uint256 p0, uint256 p1) {
        assembly {
            p0 := mload(0x40)
        }
        s = "0123456789012345678901234567890123456789";
        assembly {
            p1 := mload(0x40)
        }
    }

    function assignHex() external returns (uint256 p0, uint256 p1) {
        assembly {
            p0 := mload(0x40)
        }
        b = hex"0102";
        assembly {
            p1 := mload(0x40)
        }
    }

    function tupleAssign() external returns (uint256 p0, uint256 p1) {
        assembly {
            p0 := mload(0x40)
        }
        (s, x) = ("abc", 1);
        assembly {
            p1 := mload(0x40)
        }
    }

    function pushLiteral() external returns (uint256 p0, uint256 p1) {
        assembly {
            p0 := mload(0x40)
        }
        ss.push("abc");
        assembly {
            p1 := mload(0x40)
        }
    }

    function structField() external returns (uint256 p0, uint256 p1) {
        assembly {
            p0 := mload(0x40)
        }
        st.name = "abc";
        assembly {
            p1 := mload(0x40)
        }
    }
}
