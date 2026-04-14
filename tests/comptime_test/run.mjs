import assert from "node:assert/strict";

import {
  ada,
  copyUser,
  decodeUser,
  encodedAda,
  encodeUser,
  three,
} from "./lib/es6/src/comptime_test.mjs";

assert.equal(three, 3);
assert.deepEqual(encodedAda, {
  name: "Ada",
  age: 42,
  active: true,
});
assert.deepEqual(encodeUser(ada), encodedAda);
assert.deepEqual(decodeUser(encodedAda), ada);
assert.deepEqual(copyUser(ada), ada);
assert.equal(decodeUser("nope"), undefined);

console.log("comptime test passed");
