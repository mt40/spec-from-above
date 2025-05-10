/**
 * This is Template Data File
 * See: https://www.11ty.dev/docs/data-template-dir/
 */

export default {
	title: "Database Update Flow",
	date: "git Last Modified",
	description: `
This specification models a database update system with a producer-consumer pattern that handles message passing and failure scenarios. The system ensures data integrity by preventing older updates from overwriting newer data, while also guaranteeing progress and validity of updates.

Key features:
- Producer sends messages that represent database updates
- Consumer processes messages with compare-and-update semantics
- Handles out-of-order messages and retries
- Models failure scenarios with a failure budget
- Ensures data integrity through timestamp-based versioning`,
	tags: ["author -- preston.p@fastmail.com", "level of detail -- high"],
};
