/**
 * This is Template Data File
 * See: https://www.11ty.dev/docs/data-template-dir/
 */

export default {
	title: "Two Layered Cache",
	date: "git Last Modified",
	description: `
Quint specification for a two-layered cache system. The system consists of two cache layers (L1 and L2) that store integer values. Clients can read and write values to the cache.

The specification verifies key correctness properties like:

- read-after-write
- write-after-write
- agreement

Check with:

	quint verify \\
	two_layered_cache.qnt \\
	--invariant=readAfterWrite,writeAfterWrite \\
	--temporal=agreement

Or with TLC using the check_with_tlc.sh script from this repo:

	sh check_with_tlc.sh \\
	--file two_layered_cache.qnt \\
	--invariant readAfterWrite,writeAfterWrite \\
	--temporal agreement
	`,
	tags: ["author -- preston.p@fastmail.com", "level of detail -- low"],
};
