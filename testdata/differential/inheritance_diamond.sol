// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.0;

// Concrete bases in a diamond: D overrides both B's and C's f, and A's
// fallback; A's run reaches D's f. X's call to h names a declaration that
// Y redeclares without a body and A implements.
abstract contract X {
    function h() internal virtual returns (uint256);

    function viaH() external returns (uint256) {
        return h();
    }
}

abstract contract Y is X {
    function h() internal virtual override returns (uint256);
}

contract A is Y {
    uint256 last;

    function h() internal override returns (uint256) {
        return 7;
    }

    function f() internal virtual returns (uint256) {
        return 1;
    }

    function run() external returns (uint256) {
        last = f();
        return last;
    }

    fallback() external virtual {
        last = 100;
    }
}

contract B is A {
    function f() internal virtual override returns (uint256) {
        return 2;
    }
}

contract C is A {
    function f() internal virtual override returns (uint256) {
        return 3;
    }
}

contract D is B, C {
    function f() internal override(B, C) returns (uint256) {
        return last + 4;
    }

    fallback() external override {
        last = 200;
    }
}
