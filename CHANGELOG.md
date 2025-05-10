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
   - [x] 1.1 Modify TLA+ spec display template
   - [x] 1.2 Add logic to check for and display .cfg file

2. File Path Resolution
   - [x] 2.1 Implement path construction for .cfg files
   - [x] 2.2 Add file existence check using 11ty utilities

3. Display Logic
   - [x] 3.1 Add conditional display for TLA+ spec and config
   - [x] 3.2 Implement "This spec has no config" fallback

4. Styling
   - [x] 4.1 Implement syntax highlighting for config files
   - [x] 4.2 Support highlighting for TLA+ keywords in cfg files (e.g., "SPECIFICATION")
   - [x] 4.3 Add UI marker/separator to indicate cfg file section
   - [x] 4.4 Fix block comment highlighting for TLA+ files (e.g., (* ... *)) 