import { describe, expect, test } from "vitest";
import { AstNode, EmptyFileSystem, LangiumDocument } from 'langium';
import { createSmtServices } from "../../src/language/smt-module.js";
import { Model } from "../../src/language/generated/ast.js";
import { parseDocument } from 'langium/test';

import * as fs from 'fs';
import * as path from 'path';

const services = createSmtServices(EmptyFileSystem).Smt;
const resourceDir = path.resolve(__dirname, '../resources/smt');


describe('Single test', async () => {
    test("Single Test", async () => {
        await assertModelNoErrors(`(declare-const a Int)
        (declare-fun f (Int Bool) Int)
        (assert (< a 10))
        (assert (> (f a true) 100))
        (check-sat)
        (get-model)
      `)
    });

    test("Datatype with simple constructors", async () => {
        await assertModelNoErrors(`(declare-datatype Person (Agatha Butler Charles))
        (declare-const Killer Person)
        (assert (= Killer Agatha))
      `)
    });

    test("Complete test.smt2 file", async () => {
        const testContent = `(set-logic UF)
(declare-datatype Person (Agatha Butler Charles)) 
(declare-const Killer Person) 
(declare-fun killed (Person Person) Bool) 
(declare-fun hates (Person Person) Bool)
(declare-fun richer (Person Person) Bool)

(assert (exists ((x Person)) (killed x Agatha)))
(assert (forall ((x Person)) (forall ((y Person)) 
    (=> (killed x y) 
        (and (hates x y) (not (richer x y)))))))
(assert (forall ((x Person)) (=> (hates Agatha x) (not (hates Charles x)))))

(assert (killed Killer Agatha))
(check-sat)
(get-model)`;
        await assertModelNoErrors(testContent);
    });
});

describe('New SMT-LIB features tests', async () => {
    test("Annotated terms with !", async () => {
        await assertModelNoErrors(`(declare-const x Int)
        (assert (! (> x 0) :named positive))
        (check-sat)
      `)
    });

    test("Qualified terms with as", async () => {
        await assertModelNoErrors(`(declare-const x Real)
        (assert (= (as 5 Real) x))
        (check-sat)
      `)
    });

    test("Standard declare-sort command", async () => {
        await assertModelNoErrors(`(declare-sort Set 1)
        (declare-const s (Set Int))
        (check-sat)
      `)
    });

    test("get-unsat-assumptions command", async () => {
        const script = `(set-option :produce-unsat-assumptions true)
        (declare-const p Bool)
        (assert (! p :named assumption1))
        (assert (! (not p) :named assumption2))
        (check-sat-assuming (assumption1 assumption2))
        (get-unsat-assumptions)
      `;
        console.log("Parsing script:", script);
        const document = await parseDocument(services, script);
        const model = document.parseResult.value as Model;
        console.log("Model commands:", model.commands.length);
        model.commands.forEach((cmd: any, i: number) => {
            console.log("Command " + i + ":", cmd.$type);
            if (cmd.$type === 'CmdAssert') {
                console.log("  Assert term type:", cmd.term.$type);
                if (cmd.term.$type === 'AttributedTerm') {
                    console.log("  Attributed term attributes:", cmd.term.attribute?.length);
                    cmd.term.attribute?.forEach((attr: any, j: number) => {
                        console.log("    Attribute " + j + ":", attr.$type, attr.name || attr.keyWord);
                        if (attr.$type === 'NamedAttribute') {
                            console.log("      NamedAttribute name: " + attr.name);
                        }
                    });
                }
            }
            if (cmd.$type === 'CmdCheckSat') {
                console.log("  CheckSat propLiteral length:", cmd.propLiteral?.length);
                cmd.propLiteral?.forEach((lit: any, j: number) => {
                    console.log("    PropLiteral " + j + ":", lit);
                });
            }
        });


        await assertModelNoErrors(script);
    });

    test("Array theory operations", async () => {
        await assertModelNoErrors(`(declare-const a (Array Int Int))
        (declare-const i Int)
        (declare-const v Int)
        (assert (= (select (store a i v) i) v))
        (check-sat)
      `)
    });

    test("Bit-vector sorts", async () => {
        await assertModelNoErrors(`(declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))
        (assert (= x y))
        (check-sat)
      `)
    });

    test("Bit-vector operations", async () => {
        await assertModelNoErrors(`(declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))
        (assert (= (bvand x y) #b00000000))
        (assert (= (bvor x y) #b11111111))
        (assert (bvult x y))
        (check-sat)
      `)
    });

    test("String theory operations", async () => {
        await assertModelNoErrors(`(declare-const s String)
        (declare-const t String)
        (assert (= (str.len s) 5))
        (assert (str.contains (str.++ s t) s))
        (check-sat)
      `)
    });

    test("Extended predefined sorts", async () => {
        await assertModelNoErrors(`(declare-const s String)
        (declare-const r RegLan)
        (declare-const rm RoundingMode)
        (check-sat)
      `)
    });

    test("Extended arithmetic operators", async () => {
        await assertModelNoErrors(`(declare-const x Real)
        (declare-const y Int)
        (assert (= x (to_real y)))
        (assert (= y (to_int x)))
        (assert (is_int x))
        (check-sat)
      `)
    });

    test("Extended info flags", async () => {
        await assertModelNoErrors(`(get-info :status)
        (get-info :incremental)
        (get-info :all-statistics)
      `)
    });

    test("Indexed sorts", async () => {
        await assertModelNoErrors(`(declare-sort Matrix 2)
        (declare-const m (Matrix Int Real))
        (check-sat)
      `)
    });

    test("Complex bit-vector operations", async () => {
        await assertModelNoErrors(`(declare-const x (_ BitVec 16))
        (declare-const y (_ BitVec 16))
        (declare-const z (_ BitVec 32))
        (assert (= (concat x y) z))
        (assert (bvsle x y))
        (assert (= (bvneg x) (bvnot (bvadd x #b0000000000000001))))
        (check-sat)
      `)
    });

    test("String theory with conversions", async () => {
        await assertModelNoErrors(`(declare-const s String)
        (declare-const i Int)
        (assert (= s (str.from_int i)))
        (assert (= i (str.to_int s)))
        (assert (str.prefixof "hello" s))
        (check-sat)
      `)
    });

    test("Complex array operations", async () => {
        await assertModelNoErrors(`(declare-const a (Array Int (Array Int Bool)))
        (declare-const i Int)
        (declare-const j Int)
        (assert (select (select a i) j))
        (assert (= (store a i (store (select a i) j false)) a))
        (check-sat)
      `)
    });

    test("Mixed theory operations", async () => {
        await assertModelNoErrors(`(declare-const bv (_ BitVec 8))
        (declare-const arr (Array (_ BitVec 8) String))
        (declare-const s String)
        (assert (= (select arr bv) s))
        (assert (= (str.len s) (to_int (bv2nat bv))))
        (check-sat)
      `)
    });

    test("Complex quantified formulas with patterns", async () => {
        await assertModelNoErrors(`(declare-sort U 0)
        (declare-fun f (U U) U)
        (declare-fun p (U) Bool)
        (assert (forall ((x U) (y U)) 
          (! (=> (p x) (p (f x y))) :pattern (f x y))))
        (check-sat)
      `)
    });

    test("Let expressions with complex terms", async () => {
        await assertModelNoErrors(`(declare-const x Int)
        (assert (let ((y (+ x 1)) (z (* x 2))) 
          (and (> y x) (> z y))))
        (check-sat)
      `)
    });

    test("Full SMT-LIB script with multiple theories", async () => {
        await assertModelNoErrors(`(set-logic ALL)
        (set-info :status sat)
        (declare-sort U 0)
        (declare-const bv (_ BitVec 32))
        (declare-const s String)
        (declare-const arr (Array Int String))
        (declare-const i Int)
        
        ; Bit-vector constraints
        (assert (bvugt bv #x00000000))
        (assert (bvule bv #xFFFFFFFF))
        
        ; String constraints
        (assert (> (str.len s) 0))
        (assert (str.contains s "test"))
        
        ; Array constraints
        (assert (= (select arr i) s))
        (assert (= i (to_int (bv2nat bv))))
        
        ; Combined constraints
        (assert (= (str.len (select arr (to_int (bv2nat bv)))) 10))
        
        (check-sat)
        (get-model)
      `)
    });
});

describe('Parsing tests for FMP dataset', async () => {
    let testFiles: string[] = [];
    try {
        testFiles = fs.readdirSync(resourceDir).filter(file => file.endsWith('.smt2'));
    } catch (e) {
        console.log('No resource directory found, skipping FMP dataset tests');
    }

    if (testFiles.length === 0) {
        test('No FMP dataset files found', () => {
            expect(true).toBe(true); // Placeholder test
        });
    } else {
        for (const fileName of testFiles) {
            test(`Parsing: ${fileName}`, async () => {
                const filePath = path.join(resourceDir, fileName);
                const fileContent = fs.readFileSync(filePath, 'utf-8');
                console.log(`Parsing ${fileName}`);
                await assertModelNoErrors(fileContent);
            });
        }
    }
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