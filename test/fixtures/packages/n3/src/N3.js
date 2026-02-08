import {quad, defaultGraph, namedNode, blankNode, literalLang, literalType} from '../RDF/index.js';
import {Turtle, TriG, NTriples, NQuads} from '../N3/index.js';
import N3 from 'n3';

export const parseImpl = base => format => input => function() {
   let formatString;
   switch(format) {
      case Turtle.value:
         formatString = 'turtle';
         break;
      case TriG.value:
         formatString = 'trig';
         break;
      case NTriples.value:
         formatString = 'ntriples';
         break;
      case NQuads.value:
         formatString = 'nquads';
         break;
   }
   return parse(input, formatString, base);
}

const parse = function(input, format, base) {
   return new Promise((resolve, reject) => {
      const quads = [];
      const parser = new N3.Parser({
         format: format,
         baseIRI: base
      });

      parser.parse(input,
      (error, q) => {
         if(error) {
            reject(error);
         } else if (q) {
            let subject;
            switch(q.subject.termType) {
               case 'NamedNode':
                  subject = namedNode(q.subject.value);
                  break;
               case 'BlankNode':
                  subject = blankNode(q.subject.value);
                  break;
            }
            let predicate;
            switch(q.predicate.termType) {
               case 'NamedNode':
                  predicate = namedNode(q.predicate.value);
                  break;
            }
            let object;
            switch(q.object.termType) {
               case 'NamedNode':
                  object = namedNode(q.object.value);
                  break;
               case 'BlankNode':
                  object = blankNode(q.object.value);
                  break;
               case 'Literal':
                  if(q.object.language != "") {
                     object = literalLang(q.object.value)(q.object.language);
                  } else {
                     object = literalType(q.object.value)(namedNode(q.object.datatype.value));
                  }
                  break;
            }
            let graph;
            switch(q.graph.termType) {
               case 'NamedNode':
                  graph = namedNode(q.graph.value);
                  break;
               case 'DefaultGraph':
                  graph = defaultGraph
                  break;
            }

            quads.push(quad(subject)(predicate)(object)(graph));
         } else {
            resolve(quads);
         }
      });
   });
}

export const writeImpl = base => format => input => function() {
   let formatString;
   switch(format) {
      case Turtle.value:
         formatString = 'turtle';
         break;
      case TriG.value:
         formatString = 'trig';
         break;
      case NTriples.value:
         formatString = 'ntriples';
         break;
      case NQuads.value:
         formatString = 'nquads';
         break;
   }
   return write(input, formatString, base);
}

const write = function(input, format, base) {
   return new Promise((resolve, reject) => {
      const writer = new N3.Writer({
         format: format,
         baseIRI: base
      });

      const jsQuads = [];
      for(let q of input) {
         let subject;
         switch(q.value0.constructor.name) {
            case "NamedNode":
               subject = N3.DataFactory.namedNode(q.value0.value0);
               break;
            case "BlankNode":
               subject = N3.DataFactory.blankNode(q.value0.value0);
               break;
         }
         let predicate;
         switch(q.value1.constructor.name) {
            case "NamedNode":
               predicate = N3.DataFactory.namedNode(q.value1.value0);
               break;
         }
         let object;
         switch(q.value2.constructor.name) {
            case "NamedNode":
               object = N3.DataFactory.namedNode(q.value2.value0);
               break;
            case "BlankNode":
               object = N3.DataFactory.blankNode(q.value2.value0);
               break;
            case "LiteralLang":
               object = N3.DataFactory.literal(q.value2.value0, N3.DataFactory.namedNode(q.value2.value1.value0));
               break;
            case "LiteralType":
               object = N3.DataFactory.literal(q.value2.value0, N3.DataFactory.namedNode(q.value2.value1.value0));
               break;
         }
         let graph;
         switch(q.value3.constructor.name) {
            case "NamedNode":
               graph = N3.DataFactory.namedNode(q.value3.value0);
               break;
            case "DefaultGraph":
               graph = N3.DataFactory.defaultGraph();
               break;
         }
         writer.addQuad(N3.DataFactory.quad(subject, predicate, object, graph));
      }

      writer.end((error, result) => {
         if(error) {
            reject(error);
         } else {
            resolve(result);
         }
      });
   });
}

/*
export function fromError(a) {
  return a;
}

export function _toError(just, nothing, ref) {
  if (ref instanceof Error) {
    return just(ref);
  }
  return nothing;
}
*/