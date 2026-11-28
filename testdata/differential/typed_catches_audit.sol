// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;
contract TypedCatchesAudit {
    function rev() external pure {
        assembly {
            mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
            mstore(32, 0)
            mstore(64, 0)
            revert(0, 68)
        }
    }

    function f() external view returns (uint256) {
        assembly { mstore(64, 0) }
        try this.rev() {
            return 1;
        } catch Error(string memory) {
            return 2;
        } catch {
            return 3;
        }
    }

    function fMemory() external view returns (uint256) {
        assembly { mstore(64, 0) }
        try this.rev() {
            return 1;
        } catch Error(string memory) {
            return 2;
        } catch {
            assembly { return(64, 32) }
        }
    }

    function revMalformed() external pure {
        assembly {
            mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
            mstore(4, 0x112233445566778899aabbccddeeff00112233445566778899aabbccddeeff00)
            mstore(36, 0)
            revert(0, 68)
        }
    }

    function selectorWriteOnce() external view returns (uint256) {
        assembly { mstore(64, 0) }
        try this.revMalformed() {
            return 1;
        } catch Error(string memory) {
            return 0x1111;
        } catch Panic(uint256) {
            return 0x2222;
        } catch {
            assembly { return(0, 32) }
        }
    }
}
