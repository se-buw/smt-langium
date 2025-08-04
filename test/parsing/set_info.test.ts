import { describe, expect, test } from "vitest";
import { AstNode, EmptyFileSystem, LangiumDocument } from 'langium';
import { createSmtServices } from "../../src/language/smt-module.js";
import { Model } from "../../src/language/generated/ast.js";
import { parseDocument } from 'langium/test';

const services = createSmtServices(EmptyFileSystem).Smt;

describe('Test: set Info Parsing', () => {
    test("set Info Parsing", async () => {
        await assertModelNoErrors(`(set-info :status sat)`)
    });
});

describe('Test: produce unsat core', () => {
    test("produce unsat core", async () => {
        const testContent = `(set-option :produce-unsat-cores true)
(declare-const p Bool)
(declare-const q Bool)
(declare-const r Bool)
(declare-const s Bool)
(declare-const t Bool)
(assert (! p :named -p))
(assert (! q :named qq))
(assert (! r :named ar))
(assert (! (not (or p q)) :named fdgdfsg))
(check-sat)
(get-unsat-core)`;
        await assertModelNoErrors(testContent);
    });

    test("arithmetic operators in named", async () => {
        const script = `(set-option :produce-unsat-cores true)
(declare-const p Bool)
(assert (! p :named -p))`;
        await assertModelNoErrors(script);
    });
});


async function assertModelNoErrors(modelText: string): Promise<Model> {
    let doc: LangiumDocument<AstNode> = await parseDocument(services, modelText)
    const db = services.shared.workspace.DocumentBuilder
    console.log("Building document with validation...");
    await db.build([doc], { validation: true });
    const model = (doc.parseResult.value as Model);

    console.log("After build - checking diagnostics...");
    if (model.$document?.diagnostics && model.$document.diagnostics.length > 0) {
        console.log('Diagnostics found:');
        model.$document.diagnostics.forEach((diagnostic, index) => {
            console.log(`${index + 1}. ${diagnostic.message}`);
        });
    }

    expect(model.$document?.diagnostics?.length).toBe(0);
    return model;
}