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
  await db.build([doc], { validation: true });
  const model = (doc.parseResult.value as Model);
  
  if (model.$document?.diagnostics && model.$document.diagnostics.length > 0) {
    console.log('Diagnostics found:');
    model.$document.diagnostics.forEach((diagnostic, index) => {
      console.log(`${index + 1}. ${diagnostic.message}`);
    });
  }
  
  expect(model.$document?.diagnostics?.length).toBe(0);
  return model;
}