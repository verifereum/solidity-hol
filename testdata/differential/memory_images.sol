// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

interface IImagePeer {
    function data(uint256 n) external pure returns (uint256, uint256, uint256);
}

// Memory images: each function runs one Solidity operation and then returns
// memory from 0 to 256 bytes past the free memory pointer, so the scratch
// space, the free memory pointer, allocations and the bytes encoders leave
// past their output are all observed. A value the operation produced is
// stored at 0xe0 past the free memory pointer. (msize() would show the
// memory size too, but solc rejects it whenever the Yul optimizer runs,
// which via-IR always does.) With probe set, each function instead reverts
// with no data where its assembly starts, so the memory size the operation
// left is observed before the dump raises it. The constructor can do the
// same during creation (mode 1 dumps, mode 2 probes), where an immutable's
// value sits in memory reserved after the zero slot; an internal function
// immutable's word there is the function's number in the compiler's internal
// dispatch. Mode 3 overwrites that word with a number no function has, and
// the call through it panics with 0x51; mode 4 reads that word into the
// immutable again and dumps memory, which still holds it.
contract MemoryImages {
    struct Record {
        uint128 small;
        uint256[] items;
        bytes blob;
    }

    event Plain(uint256 indexed id, bytes data);
    event Indexed(bytes indexed key, uint256[] items);
    event Stored(bytes data, bytes indexed tag);

    uint256 immutable seed;
    function(uint256) internal pure returns (uint256) immutable op;
    mapping(uint256 => uint256) values;
    mapping(bytes => uint256) byKey;
    uint256[] items;
    bytes blob;
    Record record;
    bool probe;
    bytes tag;

    constructor(uint256 s, uint8 mode) {
        seed = s;
        op = twice;
        if (mode == 1) {
            assembly { revert(0, add(mload(0x40), 0x100)) }
        }
        if (mode == 2) {
            assembly { revert(0, 0) }
        }
        if (mode == 3) {
            assembly { mstore(0xa0, 0x99) }
            seed = op(s);
        }
        if (mode == 4) {
            assembly { mstore(0xa0, 0x99) }
            op = op;
            assembly { revert(0, add(mload(0x40), 0x100)) }
        }
    }

    function twice(uint256 x) internal pure returns (uint256) {
        return 2 * x;
    }

    function mappingRead(uint256 k) external view {
        uint256 v = values[k];
        assembly {
            if sload(probe.slot) { revert(0, 0) }
            mstore(add(mload(0x40), 0xe0), v)
            return(0, add(mload(0x40), 0x100))
        }
    }

    function bytesKeyWrite(bytes calldata k) external {
        byKey[k] = seed;
        assembly {
            if sload(probe.slot) { revert(0, 0) }
            return(0, add(mload(0x40), 0x100))
        }
    }

    function arrayPushRead(uint256 x) external {
        items.push(x);
        uint256 y = items[items.length - 1];
        assembly {
            if sload(probe.slot) { revert(0, 0) }
            mstore(add(mload(0x40), 0xe0), y)
            return(0, add(mload(0x40), 0x100))
        }
    }

    function blobStore(bytes calldata b) external {
        blob = b;
        assembly {
            if sload(probe.slot) { revert(0, 0) }
            return(0, add(mload(0x40), 0x100))
        }
    }

    function recordCopy(uint256 x, bytes calldata b) external {
        record.small = uint128(x);
        record.items.push(x);
        record.blob = b;
        Record memory r = record;
        assembly {
            if sload(probe.slot) { revert(0, 0) }
            mstore(add(mload(0x40), 0xe0), mload(r))
            return(0, add(mload(0x40), 0x100))
        }
    }

    function encodeOdd(bytes calldata b, uint256 x) external view {
        bytes memory m = b;
        bytes memory e = abi.encode(x, m);
        assembly {
            if sload(probe.slot) { revert(0, 0) }
            mstore(add(mload(0x40), 0xe0), mload(e))
            return(0, add(mload(0x40), 0x100))
        }
    }

    function encodePacked(bytes calldata b, uint16 x) external view {
        bytes memory m = b;
        bytes memory e = abi.encodePacked(m, x);
        assembly {
            if sload(probe.slot) { revert(0, 0) }
            mstore(add(mload(0x40), 0xe0), mload(e))
            return(0, add(mload(0x40), 0x100))
        }
    }

    function hashPacked(uint256 x, uint8 y) external view {
        bytes32 h = keccak256(abi.encodePacked(x, y));
        assembly {
            if sload(probe.slot) { revert(0, 0) }
            mstore(add(mload(0x40), 0xe0), byte(0, h))
            return(0, add(mload(0x40), 0x100))
        }
    }

    function emitPlain(uint256 id, bytes calldata b) external {
        bytes memory m = b;
        emit Plain(id, m);
        assembly {
            if sload(probe.slot) { revert(0, 0) }
            return(0, add(mload(0x40), 0x100))
        }
    }

    function emitIndexed(bytes calldata k, uint256 x) external {
        uint256[] memory xs = new uint256[](2);
        xs[0] = x;
        xs[1] = seed;
        emit Indexed(k, xs);
        assembly {
            if sload(probe.slot) { revert(0, 0) }
            return(0, add(mload(0x40), 0x100))
        }
    }

    // The indexed argument is read for its topic before the other is encoded.
    function emitStored(bytes calldata d, bytes calldata t) external {
        blob = d;
        tag = t;
        emit Stored(blob, tag);
        assembly {
            if sload(probe.slot) { revert(0, 0) }
            return(0, add(mload(0x40), 0x100))
        }
    }

    // An input longer than the memory written: the decoder's reads raise the
    // memory size to the last word it reads.
    function decodeFar(uint256 x) external view {
        bytes memory b = abi.encode(x);
        assembly {
            mstore(b, 0x400)
            mstore(0x40, add(b, 0x420))
        }
        (uint256 y, uint256 z) = abi.decode(b, (uint256, uint256));
        assembly {
            if sload(probe.slot) { revert(0, 0) }
            mstore(add(mload(0x40), 0xe0), add(y, z))
            return(0, add(mload(0x40), 0x100))
        }
    }

    function peerData(uint256 n) external view {
        (uint256 a, , uint256 c) = IImagePeer(address(0x5000)).data(n);
        assembly {
            if sload(probe.slot) { revert(0, 0) }
            mstore(add(mload(0x40), 0xe0), add(a, c))
            return(0, add(mload(0x40), 0x100))
        }
    }
}
