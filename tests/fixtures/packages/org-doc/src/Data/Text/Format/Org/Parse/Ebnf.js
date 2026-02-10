import { parser } from "instaparse";
import fs from 'node:fs';


const testDir = './test/examples/org-test/';
// const orgSource = '04h-formatting-properties-and-keywords';

// const testDir = './test/examples/';
// const orgSource = 'test';

function _parseOrgWithEbnf(grammarContents) {
  return function(orgText) {
    const result = parser(grammarContents)(orgText);
    return JSON.stringify({ data : result });
  };
}

function _writeEbnfJsonFor(sourceSlug) {
    return function() {

      const grammarText = fs.readFileSync('./src/Data/Text/Format/Org/Parse/org.ebnf', 'utf8');

      const orgText = fs.readFileSync(testDir + sourceSlug + '.org', 'utf8');

      const result = parser(grammarText)(orgText);
      const resultJson = JSON.stringify({ data : result });

      fs.writeFileSync(testDir + sourceSlug + '.ebnf.json', resultJson, 'utf8');
    }
}

export const parseOrgWithEbnf = _parseOrgWithEbnf;
export const writeEbnfJsonFor = _writeEbnfJsonFor;