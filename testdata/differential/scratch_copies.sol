// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

// Copies between storage and memory whose memory operand overlaps the
// scratch word [0, 32) or the free memory pointer at 0x40: the compiled
// copy writes those words as it goes (array_dataslot hashes, the pointer
// bumps of allocations), so a copy reads what it already wrote. Each
// function returns memory from 0 past the free pointer.
contract ScratchCopies {
    struct S {
        uint256[] a;
        uint256[] c;
        uint256 b;
    }

    struct P {
        uint256 x;
        uint256[] a;
    }

    uint256 pad;
    uint256[] s1;
    uint256[][] s2;
    uint256[][2] fx;
    S ss;
    bytes[2] bs2;
    bytes bb;
    P pp;

    function arrayAtZero() external {
        uint256[] memory m;
        assembly {
            m := 0
            mstore(0, 2)
            mstore(0x20, 7)
        }
        s1 = m;
        assembly { return(0, add(mload(0x40), 0x100)) }
    }

    function nestedAtZero() external {
        uint256[][] memory m = new uint256[][](1);
        assembly {
            mstore(add(m, 0x20), 0)
            mstore(0, 0)
            mstore(0x20, 7)
        }
        s2 = m;
        assembly { return(0, add(mload(0x40), 0x100)) }
    }

    function nestedSecondAtZero() external {
        uint256[][] memory m = new uint256[][](2);
        m[0] = new uint256[](1);
        m[0][0] = 5;
        assembly {
            mstore(add(m, 0x40), 0)
        }
        s2 = m;
        assembly { return(0, add(mload(0x40), 0x100)) }
    }

    function shrinkNested() external {
        s2.push();
        s2[0].push(9);
        s2 = new uint256[][](0);
        assembly { return(0, add(mload(0x40), 0x100)) }
    }

    function fixedNestedAtZero() external {
        uint256[][2] memory m;
        m[0] = new uint256[](1);
        m[0][0] = 5;
        assembly {
            mstore(add(m, 0x20), 0)
        }
        fx = m;
        assembly { return(0, add(mload(0x40), 0x100)) }
    }

    function structAtZero() external {
        S memory m;
        m.a = new uint256[](1);
        m.a[0] = 5;
        m.b = 9;
        assembly {
            mstore(add(m, 0x20), 0)
        }
        ss = m;
        assembly { return(0, add(mload(0x40), 0x100)) }
    }

    function bytesAtZero() external {
        bytes[2] memory m;
        m[0] = new bytes(32);
        m[0][0] = 0x11;
        assembly {
            mstore(add(m, 0x20), 0)
        }
        bs2 = m;
        assembly { return(0, add(mload(0x40), 0x100)) }
    }

    function bytesShrinkAtZero() external {
        bs2[0] = new bytes(40);
        bytes[2] memory m;
        m[0] = new bytes(16);
        m[0][0] = 0x22;
        assembly {
            mstore(add(m, 0x20), 0)
            mstore(0, 3)
        }
        bs2 = m;
        assembly { return(0, add(mload(0x40), 0x100)) }
    }

    function fixedTailAtZero() external {
        bs2[1] = new bytes(40);
        bytes[1] memory m;
        assembly {
            mstore(m, 0)
            mstore(0, 3)
        }
        bs2 = m;
        assembly { return(0, add(mload(0x40), 0x100)) }
    }

    function byteSequenceAtZero() external {
        bytes memory m;
        assembly {
            mstore(0, 40)
            mstore(0x20, 0xaabbcc)
            m := 0
        }
        bb = m;
        assembly { return(0, add(mload(0x40), 0x100)) }
    }

    function pushAtZero() external {
        uint256[] memory m;
        assembly {
            m := 0
            mstore(0, 0)
            mstore(0x20, 7)
        }
        s2.push(m);
        assembly { return(0, add(mload(0x40), 0x100)) }
    }

    function copyToMemoryLow() external {
        s1.push(5);
        s1.push(6);
        assembly { mstore(0x40, 0) }
        uint256[] memory xs = s1;
        assembly {
            mstore(add(mload(0x40), 0xe0), xs)
            return(0, add(mload(0x40), 0x100))
        }
    }

    function structToMemoryLow() external {
        pp.x = 3;
        pp.a.push(5);
        assembly { mstore(0x40, 0) }
        P memory q = pp;
        assembly {
            mstore(add(mload(0x40), 0xe0), q)
            return(0, add(mload(0x40), 0x100))
        }
    }

    function encodeAfterStorage() external {
        s1.push(5);
        uint256[1] memory f;
        assembly {
            f := 0
            mstore(0, 9)
        }
        bytes memory e = abi.encode(s1, f);
        assembly {
            mstore(add(mload(0x40), 0xe0), e)
            return(0, add(mload(0x40), 0x100))
        }
    }
}
