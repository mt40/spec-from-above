# Changelog

## V1.1: TLA+ Config File Display

For each TLA+ specification (*.tla file), the system should:

1. Check if there's a corresponding *.cfg file in the same directory
2. If a .cfg file exists:
   - Display the TLA+ spec code block
   - Then display the .cfg file content in a separate code block
3. If no .cfg file exists:
   - Display the TLA+ spec code block
   - Then display "This spec has no config"

This conditional display ensures users can see the configuration when available, while clearly indicating when no configuration exists.

1. Template Modification
   1.1 Modify TLA+ spec display template
   1.2 Add logic to check for and display .cfg file

2. File Path Resolution
   2.1 Implement path construction for .cfg files
   2.2 Add file existence check using 11ty utilities

3. Display Logic
   3.1 Add conditional display for TLA+ spec and config
   3.2 Implement "This spec has no config" fallback

4. Styling
   4.1 Implement syntax highlighting for config files
   4.2 Support highlighting for TLA+ keywords in cfg files (e.g., "SPECIFICATION")
   4.3 Add UI marker/separator to indicate cfg file section
   4.4 Fix block comment highlighting for TLA+ files (e.g., (* ... *))

## V2.0: TLA+ Improvements
- Fixed TLA+ angle brackets (e.g., `<<hasLock, lock, pc>>`) being incorrectly rendered as HTML tags
- Added syntax highlighting for TLA+ tokens: `<<`, `>>`, `[`, `]`, `\in`, `==`, `/\`, `\/` 