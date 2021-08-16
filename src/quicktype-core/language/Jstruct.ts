import { TargetLanguage } from "../TargetLanguage";
import { StringTypeMapping } from "../TypeBuilder";
import { TransformedStringTypeKind, PrimitiveStringTypeKind, Type, EnumType, ClassType, UnionType } from "../Type";
import { RenderContext } from "../Renderer";
import { Option, getOptionValues, OptionValues, BooleanOption } from "../RendererOptions";
import { ConvenienceRenderer, ForbiddenWordsInfo } from "../ConvenienceRenderer";
import { Namer, funPrefixNamer, Name } from "../Naming";
import {
    splitIntoWords,
    combineWords,
    firstUpperWordStyle,
    utf16LegalizeCharacters,
    allUpperWordStyle,
    allLowerWordStyle,
    stringEscape,
    originalWord,
} from "../support/Strings";
import { panic } from "../support/Support";
import { Sourcelike } from "../Source";
import { matchType, nullableFromUnion } from "../TypeUtils";
import {
    followTargetType,
} from "../Transformers";
import { arrayIntercalate, setUnionInto, mapUpdateInto, iterableSome } from "collection-utils";

const unicode = require("@mark.probst/unicode-properties");

const forbiddenTypeNames = [
    "Any",
    "True",
    "False",
    "None",
    "Enum",
    "List",
    "Dict",
    "Optional",
    "Union",
    "Iterable",
    "Type",
    "TypeVar",
    "T",
    "EnumT"
];
const forbiddenPropertyNames = [
    "and",
    "as",
    "assert",
    "async",
    "await",
    "bool",
    "break",
    "class",
    "continue",
    "datetime",
    "def",
    "del",
    "dict",
    "elif",
    "else",
    "except",
    "finally",
    "float",
    "for",
    "from",
    "global",
    "if",
    "import",
    "in",
    "int",
    "is",
    "lambda",
    "nonlocal",
    "not",
    "or",
    "pass",
    "print",
    "raise",
    "return",
    "self",
    "str",
    "try",
    "while",
    "with",
    "yield"
];

export type JstructVersion = 2 | 3;

export const pythonOptions = {
    nicePropertyNames: new BooleanOption("nice-property-names", "Transform property names to be Pythonic", true),
};

export class JstructTargetLanguage extends TargetLanguage {
    constructor(
        displayName: string = "jstruct",
        names: string[] = ["jstruct"],
        extension: string = "py"
    ) {
        super(displayName, names, extension);
    }

    protected getOptions(): Option<any>[] {
        return [pythonOptions.nicePropertyNames];
    }

    get stringTypeMapping(): StringTypeMapping {
        const mapping: Map<TransformedStringTypeKind, PrimitiveStringTypeKind> = new Map();
        const dateTimeType = "date-time";
        mapping.set("date", dateTimeType);
        mapping.set("time", dateTimeType);
        mapping.set("date-time", dateTimeType);
        mapping.set("uuid", "uuid");
        mapping.set("integer-string", "integer-string");
        mapping.set("bool-string", "bool-string");
        return mapping;
    }

    get supportsUnionsWithBothNumberTypes(): boolean {
        return true;
    }

    get supportsOptionalClassProperties(): boolean {
        return false;
    }

    needsTransformerForType(t: Type): boolean {
        if (t instanceof UnionType) {
            return iterableSome(t.members, (m: any) => this.needsTransformerForType(m));
        }
        return t.kind === "integer-string" || t.kind === "bool-string";
    }

    protected makeRenderer(renderContext: RenderContext, untypedOptionValues: { [name: string]: any }): JstructRenderer {
        const options = getOptionValues(pythonOptions, untypedOptionValues);
        return new JstructRenderer(this, renderContext, options);
    }
}

function isNormalizedStartCharacter3(utf16Unit: number): boolean {
    // FIXME: add Other_ID_Start - https://docs.python.org/3/reference/lexical_analysis.html#identifiers
    const category: string = unicode.getCategory(utf16Unit);
    return ["Lu", "Ll", "Lt", "Lm", "Lo", "Nl"].indexOf(category) >= 0;
}

function isNormalizedPartCharacter3(utf16Unit: number): boolean {
    // FIXME: add Other_ID_Continue - https://docs.python.org/3/reference/lexical_analysis.html#identifiers
    if (isNormalizedStartCharacter3(utf16Unit)) return true;
    const category: string = unicode.getCategory(utf16Unit);
    return ["Mn", "Mc", "Nd", "Pc"].indexOf(category) >= 0;
}

function isStartCharacter3(utf16Unit: number): boolean {
    const s = String.fromCharCode(utf16Unit).normalize("NFKC");
    const l = s.length;
    if (l === 0 || !isNormalizedStartCharacter3(s.charCodeAt(0))) return false;
    for (let i = 1; i < l; i++) {
        if (!isNormalizedPartCharacter3(s.charCodeAt(i))) return false;
    }
    return true;
}

function isPartCharacter3(utf16Unit: number): boolean {
    const s = String.fromCharCode(utf16Unit).normalize("NFKC");
    const l = s.length;
    for (let i = 0; i < l; i++) {
        if (!isNormalizedPartCharacter3(s.charCodeAt(i))) return false;
    }
    return true;
}

const legalizeName3 = utf16LegalizeCharacters(isPartCharacter3);

function classNameStyle(original: string): string {
    const words = splitIntoWords(original);
    return combineWords(
        words,
        legalizeName3,
        firstUpperWordStyle,
        firstUpperWordStyle,
        allUpperWordStyle,
        allUpperWordStyle,
        "",
        isStartCharacter3
    );
}

function getWordStyle(uppercase: boolean, forceSnakeNameStyle: boolean) {
    if (!forceSnakeNameStyle) {
        return originalWord;
    }
    return uppercase ? allUpperWordStyle : allLowerWordStyle;
}

function snakeNameStyle(original: string, uppercase: boolean, forceSnakeNameStyle: boolean): string {
    const wordStyle = getWordStyle(uppercase, forceSnakeNameStyle);
    const separator = forceSnakeNameStyle ? "_" : "";
    const words = splitIntoWords(original);
    return combineWords(
        words,
        legalizeName3,
        wordStyle,
        wordStyle,
        wordStyle,
        wordStyle,
        separator,
        isStartCharacter3
    );
}

export class JstructRenderer extends ConvenienceRenderer {
    private readonly imports: Map<string, Set<string>> = new Map();
    private readonly declaredTypes: Set<Type> = new Set();

    constructor(
        targetLanguage: TargetLanguage,
        renderContext: RenderContext,
        protected readonly pyOptions: OptionValues<typeof pythonOptions>
    ) {
        super(targetLanguage, renderContext);
    }

    protected forbiddenNamesForGlobalNamespace(): string[] {
        return forbiddenTypeNames;
    }

    protected forbiddenForObjectProperties(_: ClassType, _classNamed: Name): ForbiddenWordsInfo {
        return { names: forbiddenPropertyNames, includeGlobalForbidden: false };
    }

    protected makeNamedTypeNamer(): Namer {
        return funPrefixNamer("type", s => classNameStyle(s));
    }

    protected namerForObjectProperty(): Namer {
        return funPrefixNamer("property", s => snakeNameStyle(s, false, this.pyOptions.nicePropertyNames));
    }

    protected makeUnionMemberNamer(): null {
        return null;
    }

    protected makeEnumCaseNamer(): Namer {
        return funPrefixNamer("enum-case", s => snakeNameStyle(s, true, this.pyOptions.nicePropertyNames));
    }

    protected get commentLineStart(): string {
        return "# ";
    }

    protected emitDescriptionBlock(lines: Sourcelike[]): void {
        if (lines.length === 1) {
            this.emitLine('"""', lines[0], '"""');
        } else {
            this.emitCommentLines(lines, "", undefined, '"""', '"""');
        }
    }

    protected get needsTypeDeclarationBeforeUse(): boolean {
        return true;
    }

    protected canBeForwardDeclared(t: Type): boolean {
        const kind = t.kind;
        return kind === "class" || kind === "enum";
    }

    protected emitBlock(line: Sourcelike, f: () => void): void {
        this.emitLine(line);
        this.indent(f);
    }

    protected string(s: string): Sourcelike {
        const openQuote = '"';
        return [openQuote, stringEscape(s), '"'];
    }

    protected withImport(module: string, name: string): Sourcelike {
        if (true || module !== "typing") {
            // FIXME: This is ugly.  We should rather not generate that import in the first
            // place, but right now we just make the type source and then throw it away.  It's
            // not a performance issue, so it's fine, I just bemoan this special case, and
            // potential others down the road.
            mapUpdateInto(this.imports, module, (s: any) => (s ? setUnionInto(s, [name]) : new Set([name])));
        }
        return name;
    }

    protected withTyping(name: string): Sourcelike {
        return this.withImport("typing", name);
    }

    protected withStruct(name: string): Sourcelike {
        return this.withImport("jstruct", name);
    }

    protected namedType(t: Type): Sourcelike {
        const name = this.nameForNamedType(t);
        if (this.declaredTypes.has(t)) return name;
        return ["'", name, "'"];
    }

    protected pythonType(t: Type, struct: boolean = true): Sourcelike {
        const actualType = followTargetType(t);
        return matchType<Sourcelike>(
            actualType,
            _anyType => this.withTyping("Any"),
            _nullType => "None",
            _boolType => "bool",
            _integerType => "int",
            _doubletype => "float",
            _stringType => "str",
            arrayType => [this.withTyping("List"), "[", this.pythonType(arrayType.items, false), "] = ", this.withStruct("JList"), "[", this.pythonType(arrayType.items, false), "]"],
            classType => struct ? [this.namedType(classType), " = ", this.withStruct("JStruct"), "[", this.pythonType(classType, false), "]"] : this.namedType(classType),
            mapType => [this.withTyping("Dict"), "[str, ", this.pythonType(mapType.values, false), "] = ", this.withStruct("JDict"), "[str, ", this.pythonType(mapType.values, false), "]"],
            enumType => this.namedType(enumType),
            unionType => {
                const maybeNullable = nullableFromUnion(unionType);
                if (maybeNullable !== null) {
                    let rest: string[] = [];
                    let isStruct = ['array', 'class'].filter(k => maybeNullable.kind == k).length > 0;
                    if (!this.getAlphabetizeProperties() && !isStruct) rest.push(" = None");

                    if (maybeNullable.kind === 'class') {
                        return [this.withTyping("Optional"), "[", this.pythonType(maybeNullable, false), "] = ", this.withStruct("JStruct"), "[", this.pythonType(maybeNullable, false), "]"];
                    }
                    if (maybeNullable.kind === 'array') {
                        return [this.pythonType(maybeNullable, false)];
                    }

                    return [this.withTyping("Optional"), "[", this.pythonType(maybeNullable, false), "]", ...rest];
                }
                const memberTypes = Array.from(unionType.sortedMembers).map(m => this.pythonType(m, false));
                return [this.withTyping("Union"), "[", arrayIntercalate(", ", memberTypes), "]"];
            },
            transformedStringType => {
                if (transformedStringType.kind === "date-time") {
                    return this.withImport("datetime", "datetime");
                }
                if (transformedStringType.kind === "uuid") {
                    return this.withImport("uuid", "UUID");
                }
                return panic(`Transformed type ${transformedStringType.kind} not supported`);
            }
        );
    }

    protected declarationLine(t: Type): Sourcelike {
        if (t instanceof ClassType) {
            return ["class ", this.nameForNamedType(t), ":"];
        }
        if (t instanceof EnumType) {
            return ["class ", this.nameForNamedType(t), "(", this.withImport("enum", "Enum"), "):"];
        }
        return panic(`Can't declare type ${t.kind}`);
    }

    protected declareType<T extends Type>(t: T, emitter: () => void): void {
        this.emitBlock(this.declarationLine(t), () => {
            this.emitDescription(this.descriptionForType(t));
            emitter();
        });
        this.declaredTypes.add(t);
    }

    protected typeHint(...sl: Sourcelike[]): Sourcelike {
        return sl;
    }

    protected typingDecl(name: Sourcelike, type: string): Sourcelike {
        return [name, this.typeHint(": ", this.withTyping(type))];
    }

    protected typingReturn(type: string): Sourcelike {
        return this.typeHint(" -> ", this.withTyping(type));
    }

    protected emitClass(t: ClassType): void {
        this.emitLine("@", this.withImport("attr", "s"), "(auto_attribs=True)");
        this.declareType(t, () => {
            if (t.getProperties().size === 0) {
                this.emitLine("pass");
            } else {
                this.forEachClassProperty(t, "none", (name, jsonName, cp) => {
                    this.emitDescription(this.descriptionForClassProperty(t, jsonName));
                    this.emitLine(name, this.typeHint(": ", this.pythonType(cp.type)));
                });
            }
            this.ensureBlankLine();
        });
    }

    protected emitEnum(t: EnumType): void {
        this.declareType(t, () => {
            this.forEachEnumCase(t, "none", (name, jsonName) => {
                this.emitLine([name, " = ", this.string(jsonName)]);
            });
        });
    }

    protected emitImports(): void {
        this.imports.forEach((names, module) => {
            this.emitLine("from ", module, " import ", Array.from(names).join(", "));
        });
    }

    protected emitSupportCode(): void {
        return;
    }

    protected emitClosingCode(): void {
        return;
    }

    protected emitSourceStructure(_givenOutputFilename: string): void {
        const declarationLines = this.gatherSource(() => {
            this.forEachNamedType(
                ["interposing", 2],
                (c: ClassType) => this.emitClass(c),
                e => this.emitEnum(e),
                _u => {
                    return;
                }
            );
        });

        const closingLines = this.gatherSource(() => this.emitClosingCode());
        const supportLines = this.gatherSource(() => this.emitSupportCode());

        if (this.leadingComments !== undefined) {
            this.emitCommentLines(this.leadingComments);
        }
        this.ensureBlankLine();
        this.emitImports();
        this.ensureBlankLine(2);
        this.emitGatheredSource(supportLines);
        this.ensureBlankLine(2);
        this.emitGatheredSource(declarationLines);
        this.ensureBlankLine(2);
        this.emitGatheredSource(closingLines);
    }
}
