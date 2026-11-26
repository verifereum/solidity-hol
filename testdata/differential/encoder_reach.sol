// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

interface IReachPeer {
    function take(bytes calldata b) external pure returns (uint256);
}

// Encoder inputs that end at or below an unaligned free memory pointer.
// Assembly leaves the pointer 24 bytes past a word boundary (0x98), so an
// input allocated there ends at the new pointer while the word holding its
// last byte reaches past it: an empty byte sequence (which = 0), a 30-byte
// string constant (which = 1), and memory arrays and a struct whose last
// word ends at the pointer. Each function then returns memory from 0 to 256
// bytes past the free memory pointer (msize() doesn't compile under via-IR);
// with probe set, it reverts with no data where its dump starts, so the
// memory size the operation left is observed.
contract EncoderReach {
    struct Pair {
        uint256 a;
        uint256 b;
    }

    uint256 private probe;
    string private constant LABEL = "a thirty byte constant label..";

    event Data(bytes b);
    event Indexed(bytes indexed b);
    event Words(uint256[] a);
    event IndexedWords(uint256[] indexed a);
    event Fixed(uint256[2] a);
    event IndexedFixed(uint256[2] indexed a);
    event Paired(Pair p);
    event IndexedPair(Pair indexed p);
    event Keyed(bytes indexed k, bytes b);

    error Refused(bytes b);

    function input(uint256 which) private pure returns (bytes memory b) {
        assembly { mstore(0x40, 0x98) }
        if (which == 0) {
            b = new bytes(0);
        } else {
            b = bytes(LABEL);
        }
    }

    function words() private pure returns (uint256[] memory a) {
        assembly { mstore(0x40, 0x98) }
        a = new uint256[](2);
        a[0] = 1;
        a[1] = 2;
    }

    function fixedWords() private pure returns (uint256[2] memory a) {
        assembly { mstore(0x40, 0x98) }
        uint256[2] memory f;
        f[0] = 3;
        f[1] = 4;
        a = f;
    }

    function pair() private pure returns (Pair memory p) {
        assembly { mstore(0x40, 0x98) }
        p = Pair(5, 6);
    }

    function dump() private view {
        assembly {
            if sload(probe.slot) { revert(0, 0) }
            return(0, add(mload(0x40), 0x100))
        }
    }

    function encode(uint256 which) external view {
        bytes memory e = abi.encode(input(which));
        e;
        dump();
    }

    function packed(uint256 which) external view {
        bytes memory e = abi.encodePacked(input(which));
        e;
        dump();
    }

    function refuse(uint256 which) external pure {
        revert Refused(input(which));
    }

    function forward(uint256 which) external view {
        uint256 n = IReachPeer(address(0x5000)).take(input(which));
        assembly { mstore(add(mload(0x40), 0xe0), n) }
        dump();
    }

    function give(uint256 which) external pure returns (bytes memory) {
        return input(which);
    }

    function emitData(uint256 which) external {
        emit Data(input(which));
        dump();
    }

    function emitIndexed(uint256 which) external {
        emit Indexed(input(which));
        dump();
    }

    function wordsEncode() external view {
        bytes memory e = abi.encode(words());
        e;
        dump();
    }

    function wordsPacked() external view {
        bytes memory e = abi.encodePacked(words());
        e;
        dump();
    }

    function wordsEmit() external {
        uint256[] memory a = words();
        emit Words(a);
        emit IndexedWords(a);
        dump();
    }

    function fixedEncode() external view {
        bytes memory e = abi.encode(fixedWords());
        e;
        dump();
    }

    function fixedPacked() external view {
        bytes memory e = abi.encodePacked(fixedWords());
        e;
        dump();
    }

    function fixedEmit() external {
        uint256[2] memory a = fixedWords();
        emit Fixed(a);
        emit IndexedFixed(a);
        dump();
    }

    function pairEncode() external view {
        bytes memory e = abi.encode(pair());
        e;
        dump();
    }

    function pairEmit() external {
        Pair memory p = pair();
        emit Paired(p);
        emit IndexedPair(p);
        dump();
    }

    // A 5-byte sequence at 0, ending at 37, and the free memory pointer at
    // 0x28. The indexed key's hash preimage, written at the pointer, sets it
    // to the key's last word, where the emit then encodes b: at or past 37
    // the encoding leaves b intact.
    function emitKeyed(bytes calldata k) external {
        bytes memory b;
        assembly {
            mstore(0, 5)
            mstore(0x20, 0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20)
            b := 0
            mstore(0x40, 0x28)
        }
        emit Keyed(k, b);
        assembly {
            if sload(probe.slot) { revert(0, 0) }
            return(0, 0x200)
        }
    }
}
