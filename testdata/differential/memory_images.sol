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
// which via-IR always does.) The constructor can do the same during creation, where an
// immutable's value sits in memory reserved after the zero slot.
contract MemoryImages {
    struct Record {
        uint128 small;
        uint256[] items;
        bytes blob;
    }

    event Plain(uint256 indexed id, bytes data);
    event Indexed(bytes indexed key, uint256[] items);

    uint256 immutable seed;
    mapping(uint256 => uint256) values;
    mapping(bytes => uint256) byKey;
    uint256[] items;
    bytes blob;
    Record record;

    constructor(uint256 s, bool dump) {
        seed = s;
        if (dump) {
            assembly { revert(0, add(mload(0x40), 0x100)) }
        }
    }

    function mappingRead(uint256 k) external view {
        uint256 v = values[k];
        assembly {
            mstore(add(mload(0x40), 0xe0), v)
            return(0, add(mload(0x40), 0x100))
        }
    }

    function bytesKeyWrite(bytes calldata k) external {
        byKey[k] = seed;
        assembly { return(0, add(mload(0x40), 0x100)) }
    }

    function arrayPushRead(uint256 x) external {
        items.push(x);
        uint256 y = items[items.length - 1];
        assembly {
            mstore(add(mload(0x40), 0xe0), y)
            return(0, add(mload(0x40), 0x100))
        }
    }

    function blobStore(bytes calldata b) external {
        blob = b;
        assembly { return(0, add(mload(0x40), 0x100)) }
    }

    function recordCopy(uint256 x, bytes calldata b) external {
        record.small = uint128(x);
        record.items.push(x);
        record.blob = b;
        Record memory r = record;
        assembly {
            mstore(add(mload(0x40), 0xe0), mload(r))
            return(0, add(mload(0x40), 0x100))
        }
    }

    function encodeOdd(bytes calldata b, uint256 x) external pure {
        bytes memory m = b;
        bytes memory e = abi.encode(x, m);
        assembly {
            mstore(add(mload(0x40), 0xe0), mload(e))
            return(0, add(mload(0x40), 0x100))
        }
    }

    function encodePacked(bytes calldata b, uint16 x) external pure {
        bytes memory m = b;
        bytes memory e = abi.encodePacked(m, x);
        assembly {
            mstore(add(mload(0x40), 0xe0), mload(e))
            return(0, add(mload(0x40), 0x100))
        }
    }

    function hashPacked(uint256 x, uint8 y) external pure {
        bytes32 h = keccak256(abi.encodePacked(x, y));
        assembly {
            mstore(add(mload(0x40), 0xe0), byte(0, h))
            return(0, add(mload(0x40), 0x100))
        }
    }

    function emitPlain(uint256 id, bytes calldata b) external {
        bytes memory m = b;
        emit Plain(id, m);
        assembly { return(0, add(mload(0x40), 0x100)) }
    }

    function emitIndexed(bytes calldata k, uint256 x) external {
        uint256[] memory xs = new uint256[](2);
        xs[0] = x;
        xs[1] = seed;
        emit Indexed(k, xs);
        assembly { return(0, add(mload(0x40), 0x100)) }
    }

    function peerData(uint256 n) external view {
        (uint256 a, , uint256 c) = IImagePeer(address(0x5000)).data(n);
        assembly {
            mstore(add(mload(0x40), 0xe0), add(a, c))
            return(0, add(mload(0x40), 0x100))
        }
    }
}
