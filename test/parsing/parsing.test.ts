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
});

describe('Parsing tests for FMP dataset', async () => {
  const testFiles = fs.readdirSync(resourceDir).filter(file => file.endsWith('.smt2'));
  for (const fileName of testFiles) {
    test(`Parsing: ${fileName}`, async () => {
      const filePath = path.join(resourceDir, fileName);
      const fileContent = fs.readFileSync(filePath, 'utf-8');
      console.log(`Parsing ${fileName}`);
      await assertModelNoErrors(fileContent);
    });
  }
});

async function assertModelNoErrors(modelText: string): Promise<Model> {
  let doc: LangiumDocument<AstNode> = await parseDocument(services, modelText)
  const db = services.shared.workspace.DocumentBuilder
  await db.build([doc], { validation: true });
  const model = (doc.parseResult.value as Model);
  expect(model.$document?.diagnostics?.length).toBe(0);
  return model;
}