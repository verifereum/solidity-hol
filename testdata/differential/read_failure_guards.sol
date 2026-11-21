// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

contract ReadFailureGuards {
    enum E { A, B }
    struct S { uint256 x; E e; }

    error Err(uint256, E[1]);
    event Ev(bytes indexed a, bytes indexed c, E[] indexed b);
    event Stored(bytes indexed k, uint256[] v);

    E[] s;
    S t;
    E[2] u;
    E[33] w;
    uint256[] items;

    // Encoder: reading a failing input at the free memory pointer.
    function encoderOverlapReturn() public pure returns (uint256, E[1] memory) {
        E[1] memory a;
        assembly {
            a := mload(0x40)
            mstore(a, 2)
        }
        return (0, a);
    }

    function encoderOverlapFirst() public pure returns (E[1] memory, uint256) {
        E[1] memory a;
        assembly {
            a := mload(0x40)
            mstore(a, 2)
        }
        return (a, 0);
    }

    // Encoder: an earlier valid input at/above the free pointer overwritten
    // before a later failing read (calldata enum validation).
    function encoderEarlierValidOverlap(E[] calldata bad)
        public pure returns (bytes memory)
    {
        E[1] memory a;
        assembly {
            a := add(mload(0x40), 32)
            mstore(a, 0)
        }
        return abi.encode(uint256(2), a, bad);
    }

    // Packed encoder: earlier valid memory bytes above the free pointer,
    // later failing enum array below it.
    function packedEarlierValidOverlap() public pure returns (bytes memory) {
        bytes memory a;
        E[1] memory b;
        assembly {
            mstore(b, 2)
            a := add(mload(0x40), 32)
            mstore(a, 1)
            mstore(add(a, 32), 0)
        }
        return abi.encodePacked(a, b);
    }

    // Revert error payload: failing input at the free pointer + 4.
    function revertOverlap() public pure {
        E[1] memory a;
        assembly {
            a := add(mload(0x40), 4)
            mstore(a, 2)
        }
        revert Err(0, a);
    }

    // Event: indexed hash preimage overwrites the free pointer before a later
    // failing read.
    function emitPointerMove(bytes calldata c) external {
        bytes memory a;
        E[] memory b;
        assembly {
            mstore(0, 1)
            mstore(0x20, 5)
            a := 0
            b := 0
            mstore(0x40, 0x41)
        }
        emit Ev(a, c, b);
    }

    // Event: an indexed hash preimage moves the free pointer into scratch, so
    // the compiled encoder writes the log's data where hashing the stored
    // array's slot later overwrites it.
    function emitStoredPointerMove(bytes calldata k) external {
        assembly { mstore(0x40, 0x40) }
        emit Stored(k, items);
    }

    // Agreeing controls: all reads below the free pointer, pointer unmoved.
    function emitStored(bytes calldata k) external {
        emit Stored(k, items);
    }

    function encoderBelowFpPanics() public pure returns (uint256, E[1] memory) {
        E[1] memory a;
        assembly {
            mstore(a, 2)
        }
        return (0, a);
    }

    function packedBelowFpPanics() public pure returns (bytes memory) {
        bytes memory a = hex"01";
        E[1] memory b;
        assembly {
            mstore(b, 2)
        }
        return abi.encodePacked(a, b);
    }

    function emitBelowFpPanics(bytes calldata c) external {
        bytes memory a = hex"00";
        E[] memory b = new E[](1);
        assembly {
            mstore(add(b, 32), 5)
        }
        emit Ev(a, c, b);
    }

    // Non-static storage copy controls (static-frame variants are tested in
    // solidityEvaluatorTest).
    function copyDyn() external {
        E[] memory m = new E[](1);
        assembly { mstore(add(m, 32), 5) }
        s = m;
    }

    function copyStruct() external {
        S memory m = S(7, E.A);
        assembly { mstore(add(m, 32), 5) }
        t = m;
    }

    function copyFixed() external {
        E[2] memory m;
        assembly { mstore(add(m, 32), 5) }
        u = m;
    }

    function copyFixed2() external {
        E[33] memory m;
        assembly { mstore(add(m, 1024), 5) }
        w = m;
    }

    function selfCopy() external returns (uint256) {
        s = s;
        return s.length;
    }
}
