<div align="center">
  <!-- <img src="./frontend/public/logo_se.png" width="100px" /> -->
  <h1>A Language Server and Tooling for SMT-LIB 2</h1>
  <p>A <a href="https://langium.org/">Langium</a>-based language tooling project for SMT-LIB 2 scripts. </p>

  <p>The LSP is integrated into <a href="https://play.formal-methods.net/">FM Playground</a> demonstrating the language features in a browser environment.</p>
  <a href="https://play.formal-methods.net/"><img src="https://img.shields.io/website?url=https%3A%2F%2Fplay.formal-methods.net%2F&label=play.formal-methods.net" alt="FM Playground"></a>
  <img src="https://img.shields.io/github/issues/se-buw/smt-langium" alt="GitHub issues">
  <img src="https://img.shields.io/github/license/se-buw/smt-langium" alt="GitHub License">
  <hr>
</div>


## Features

- **Full SMT-LIB 2 grammar** — commands, sorts, terms, attributes, options, and info flags as defined in the standard.
- **Z3 solver extensions** — `declare-const`, `declare-sort` arity variants, Z3 datatype declarations, `eval`, `maximize`/`minimize`, and Z3-style option keywords.
- **Cross-reference resolution** — Declared constants, functions, sorts, datatypes, constructors, and named attributes are resolved across the file via a custom scope computation.
- **IntelliSense / Code completion** — Keyword completions, Boolean literal completions (`true`/`false`), and symbol placeholder completions.

---

## Prerequisites

| Requirement | Version                                  |
| ----------- | ---------------------------------------- |
| Node.js     | ≥ 18.0.0 (18.19.1 recommended via Volta) |
| npm         | ≥ 10.2.4 (via Volta)                     |

## Installation

```bash
# Clone the repository
git clone https://github.com/se-buw/smt-langium.git
cd smt-langium

# Install dependencies
npm install

# Generate the Langium parser and build
npm run langium:generate
npm run build
```

## Project Structure

```
smt-langium/
├── bin/
│   └── cli.js                   # CLI entry point
├── src/
│   ├── extension/
│   │   └── main.ts              # VS Code extension activation/deactivation
│   ├── language/
│   │   ├── smt.langium          # Grammar definition (source of truth)
│   │   ├── smt-module.ts        # Langium DI module & service factory
│   │   ├── smt-completion-provider.ts  # Custom LSP completion provider
│   │   ├── smt-scope-computation.ts    # Custom cross-reference scope logic
│   │   ├── smt-validator.ts     # Custom AST validation checks
│   │   ├── main.ts              # Language server entry (Node)
│   │   └── main-browser.ts      # Language server entry (browser/Monaco)
│   ├── cli/
│   │   ├── main.ts              # CLI command definitions (commander)
│   │   ├── generator.ts         # Code generation stub
│   │   └── cli-util.ts          # File/path helpers for CLI
│   ├── setupCommon.ts           # Shared Monaco worker + client config
│   ├── setupClassic.ts          # Classic Monaco editor setup
│   └── setupExtended.ts         # Extended Monaco editor setup
├── test/
│   └── parsing/
│       ├── parsing.test.ts      # Main parsing test suite (vitest)
│       └── set_info.test.ts     # set-info / unsat-core tests
├── static/
│   ├── monacoClassic.html       # Standalone web editor (classic)
│   ├── monacoExtended.html      # Standalone web editor (extended)
│   └── styles.css
├── langium-config.json          # Langium generator configuration
├── language-configuration.json  # VS Code language configuration
├── tsconfig.json
├── tsconfig.src.json
├── esbuild.mjs                  # esbuild bundling script
└── vite.config.ts               # Vite config for web bundle
```

### Generated files

Running `npm run langium:generate` populates `src/language/generated/` with:

- `ast.ts` — TypeScript types for all AST nodes
- `module.ts` — Generated Langium DI modules
- `grammar.ts` — Serialised grammar
- `../syntaxes/smt.monarch.ts` — Monarch tokenizer for Monaco
- `syntaxes/smt.tmLanguage.json` — TextMate grammar for VS Code

## Development

### Build

```bash
# Generate Langium parser artifacts and compile TypeScript + bundle
npm run build
```

This runs two steps:

1. `langium generate` — reads `langium-config.json`, processes `src/language/smt.langium`, and writes generated files to `src/language/generated/` and `syntaxes/`.
2. `tsc -b tsconfig.src.json && node esbuild.mjs` — compiles TypeScript and bundles the language server with esbuild.

### Watch Mode

```bash
# Watch for grammar and TypeScript changes simultaneously
npm run watch
```

Runs `tsc` and `esbuild` in parallel with `concurrently`, colour-coded for easy identification.

To only watch the grammar:

```bash
npm run langium:watch
```

### Testing

Tests are written with [Vitest](https://vitest.dev/) and live in `test/parsing/`.

```bash
npm test
```
