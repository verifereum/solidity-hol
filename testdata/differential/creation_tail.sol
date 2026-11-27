// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.37;
import "./creation_tail_child.sol";

contract CreationTail {
    function tryCreate(uint256 n) external returns (bool ok, uint256 v, string memory reason) {
        try new TailChild(n) returns (TailChild c) {
            return (true, c.value(), "");
        } catch Error(string memory s) {
            return (false, 0, s);
        } catch Panic(uint256 code) {
            return (false, code, "");
        }
    }

    function tryBare(uint256 n) external returns (bool) {
        try new TailChild(n) {
            return true;
        } catch {
            return false;
        }
    }

    function tryValue(uint256 n) external returns (bool, uint256) {
        try new TailChild{value: 1}(n) returns (TailChild c) {
            return (true, c.value());
        } catch (bytes memory data) {
            return (false, data.length);
        }
    }

    function trySalted(uint256 n, bytes32 salt) external returns (bool first, bool second) {
        try new TailChild{salt: salt}(n) {
            first = true;
        } catch {}
        try new TailChild{salt: salt}(n) {
            second = true;
        } catch {}
    }

    // the word after the copy, over memory dirtied first: the copy writes
    // the code's bytes only, so the dirty bytes after them stay
    function runtimePadding() external pure returns (uint256 size, bytes32 tail) {
        assembly {
            let p := mload(0x40)
            mstore(add(p, 224), not(0))
            mstore(add(p, 256), not(0))
        }
        bytes memory code = type(TailChild).runtimeCode;
        assembly {
            tail := mload(add(add(code, 32), mload(code)))
        }
        size = code.length;
    }

    // as runtimePadding, for the creation code
    function creationPadding() external pure returns (uint256 size, bytes32 tail) {
        assembly {
            let p := mload(0x40)
            for { let i := 0 } lt(i, 0x400) { i := add(i, 32) } { mstore(add(p, i), not(0)) }
        }
        bytes memory code = type(TailChild).creationCode;
        assembly {
            tail := mload(add(add(code, 32), mload(code)))
        }
        size = code.length;
    }

    function runtime() external returns (uint256 size, bool deployed) {
        bytes memory code = type(TailChild).runtimeCode;
        TailChild c = new TailChild(1);
        return (code.length, address(c).codehash == keccak256(code));
    }
}
