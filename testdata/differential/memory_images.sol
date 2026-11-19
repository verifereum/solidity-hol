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
// the call through it panics with 0x51; mode 4 reads that word into a local,
// overwrites the reserved word again, assigns the local back to the immutable
// and dumps memory, which holds the first word; mode 5 does the same and
// reverts with no data instead of dumping.
contract Doomed {
    constructor() {
        revert("a reason longer than one memory word, forwarded");
    }
}

contract Refuser {
    receive() external payable {
        revert("refused, with a reason past one word");
    }
}

contract MemoryImages {
    struct Record {
        uint128 small;
        uint256[] items;
        bytes blob;
    }

    struct Pair {
        bytes b;
        uint256[] a;
    }

    event Plain(uint256 indexed id, bytes data);
    event Indexed(bytes indexed key, uint256[] items);
    event Stored(bytes data, bytes indexed tag);
    event Paired(Pair indexed p);
    event Tagged(bytes indexed key, uint256 value);

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
            function(uint256) internal pure returns (uint256) kept = op;
            assembly { mstore(0xa0, 0x77) }
            op = kept;
            assembly { revert(0, add(mload(0x40), 0x100)) }
        }
        if (mode == 5) {
            assembly { mstore(0xa0, 0x99) }
            function(uint256) internal pure returns (uint256) kept = op;
            assembly { mstore(0xa0, 0x77) }
            op = kept;
            assembly { revert(0, 0) }
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

    // A literal key is packed for its hash at the free memory pointer too.
    function literalKeyWrite() external {
        byKey["a literal key longer than one memory word"] = seed;
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

    // The copy into storage reads a memory source in whole words, so from
    // an unaligned one-byte array it touches the word after the byte too.
    function blobStoreUnaligned() external {
        bytes memory m;
        assembly {
            m := 161
            mstore(161, 1)
            mstore8(193, 0xab)
        }
        blob = m;
        assembly {
            if sload(probe.slot) { revert(0, 0) }
            return(0, add(mload(0x40), 0x100))
        }
    }

    // A struct copied into storage copies each byte sequence member with the
    // same whole-word loop, so an unaligned member touches the word after
    // its last byte too.
    function recordStoreUnaligned() external {
        Record memory r;
        bytes memory m;
        assembly {
            m := add(mload(0x40), 1)
            mstore(m, 1)
            mstore8(add(m, 0x20), 0xab)
        }
        r.blob = m;
        record = r;
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

    // An indexed struct hashes its in-place encoding; the word cleared after
    // copying b lies past the encoding when the array after it is empty.
    function emitPair(bytes calldata b) external {
        Pair memory p = Pair(b, new uint256[](0));
        emit Paired(p);
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

    // The decoder compares the input's length with the heads' as signed
    // words, so a length word of 2^255 or more reverts.
    function decodeHuge(uint256 x) external view {
        bytes memory b = abi.encode(x);
        assembly { mstore(b, shl(255, 1)) }
        uint256 y = abi.decode(b, (uint256));
        assembly {
            mstore(add(mload(0x40), 0xe0), y)
            return(0, add(mload(0x40), 0x100))
        }
    }

    // The precompile reads its input after the scratch word is zeroed, so
    // with the free memory pointer below 32 it sees a digest with zeroed bytes
    // (and the encoding overwrites the free memory pointer itself).
    function recover(bytes32 h, uint8 v, bytes32 r, bytes32 s, bool low) external view {
        if (low) {
            assembly { mstore(0x40, 0x10) }
        }
        address a = ecrecover(h, v, r, s);
        assembly {
            if sload(probe.slot) { revert(0, 0) }
            if low {
                mstore(0, a)
                return(0, 0x20)
            }
            mstore(add(mload(0x40), 0xe0), a)
            return(0, add(mload(0x40), 0x100))
        }
    }

    // An ordinary return: the dispatcher encodes the value at the free memory
    // pointer, so the memory size covers it.
    function plainReturn(uint256 x) external pure returns (uint256) {
        return x + 1;
    }

    function failing(uint256 n) external pure returns (bytes memory) {
        require(n == 0, "a reason longer than one memory word, forwarded");
        return "";
    }

    // An uncaught failed call: the compiled code copies the callee's revert
    // data to the free memory pointer and reverts with it.
    function forwardRevert(uint256 n) external view {
        this.failing(n);
    }

    // sha256 packs its operand for the precompile where the operand is,
    // without copying it to memory first.
    function digestCalldata(bytes calldata d) external view {
        bytes32 h = sha256(d);
        assembly {
            if sload(probe.slot) { revert(0, 0) }
            mstore(add(mload(0x40), 0xe0), h)
            return(0, add(mload(0x40), 0x100))
        }
    }

    function digestLiteral() external view {
        bytes32 h = sha256("a literal longer than one word, packed in place");
        assembly {
            if sload(probe.slot) { revert(0, 0) }
            mstore(add(mload(0x40), 0xe0), h)
            return(0, add(mload(0x40), 0x100))
        }
    }

    function digestStored(bytes calldata d) external {
        blob = d;
        bytes32 h = sha256(blob);
        assembly {
            if sload(probe.slot) { revert(0, 0) }
            mstore(add(mload(0x40), 0xe0), h)
            return(0, add(mload(0x40), 0x100))
        }
    }

    // A try whose clauses do not match the failure forwards it the same way.
    function forwardTry(uint256 n) external view {
        try this.failing(n) returns (bytes memory) {
        } catch Panic(uint256) {
        }
    }

    // With the free memory pointer at 0x20, the indexed key's hash preimage
    // overwrites the pointer, which the emit reads again before it encodes
    // the log's data.
    function emitLow(bytes calldata k, uint256 x) external {
        assembly { mstore(0x40, 0x20) }
        emit Tagged(k, x);
        assembly {
            if sload(probe.slot) { revert(0, 0) }
            return(0, add(mload(0x40), 0x100))
        }
    }

    // A low-level call packs calldata or storage data at the free memory
    // pointer, where it would send a memory byte sequence from where it is.
    function rawCallCalldata(bytes calldata b) external {
        (bool ok, ) = address(0x5000).call(b);
        assembly {
            if sload(probe.slot) { revert(0, 0) }
            mstore(add(mload(0x40), 0xe0), ok)
            return(0, add(mload(0x40), 0x100))
        }
    }

    function rawCallStored(bytes calldata b) external {
        blob = b;
        (bool ok, ) = address(0x5000).call(blob);
        assembly {
            if sload(probe.slot) { revert(0, 0) }
            mstore(add(mload(0x40), 0xe0), ok)
            return(0, add(mload(0x40), 0x100))
        }
    }

    // A call's results are decoded from memory after the free memory pointer
    // moves past them, so with the pointer set into the return data the new
    // pointer overwrites returned words before they are decoded.
    function peerDataLow(uint256 n) external view {
        assembly { mstore(0x40, 0x30) }
        (uint256 a, uint256 b, uint256 c) = IImagePeer(address(0x5000)).data(n);
        assembly {
            if sload(probe.slot) { revert(0, 0) }
            mstore(add(mload(0x40), 0xe0), add(a, add(b, c)))
            mstore(add(mload(0x40), 0xc0), b)
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

// Forwarded revert data after a failed creation or transfer. A contract that
// creates others has creation objects inside its Yul object, so these live
// apart from MemoryImages, whose Yul runs in the three-way check.
contract MemoryForwarding {
    // A failed creation copies the constructor's revert data to the free
    // memory pointer and reverts with it.
    function forwardCreate() external {
        new Doomed();
    }

    // So does a failed transfer.
    function forwardTransfer() external {
        Refuser r = new Refuser();
        payable(address(r)).transfer(0);
    }
}
