import { Assert } from '../abstract-ops/all.mts';
// @ts-expect-error
import UnicodeSets from '../data-gen.json';

export { UnicodeSets };

// #table-nonbinary-unicode-properties
export const NonbinaryUnicodeProperties = {
  General_Category: 'General_Category',
  gc: 'General_Category',
  Script: 'Script',
  sc: 'Script',
  Script_Extensions: 'Script_Extensions',
  scx: 'Script_Extensions',
} as const;
Object.setPrototypeOf(NonbinaryUnicodeProperties, null);

// #table-binary-unicode-properties
export const BinaryUnicodeProperties = {
  ASCII: 'ASCII',
  ASCII_Hex_Digit: 'ASCII_Hex_Digit',
  AHex: 'ASCII_Hex_Digit',
  Alphabetic: 'Alphabetic',
  Alpha: 'Alphabetic',
  Any: 'Any',
  Assigned: 'Assigned',
  Bidi_Control: 'Bidi_Control',
  Bidi_C: 'Bidi_Control',
  Bidi_Mirrored: 'Bidi_Mirrored',
  Bidi_M: 'Bidi_Mirrored',
  Case_Ignorable: 'Case_Ignorable',
  CI: 'Case_Ignorable',
  Cased: 'Cased',
  Changes_When_Casefolded: 'Changes_When_Casefolded',
  CWCF: 'Changes_When_Casefolded',
  Changes_When_Casemapped: 'Changes_When_Casemapped',
  CWCM: 'Changes_When_Casemapped',
  Changes_When_Lowercased: 'Changes_When_Lowercased',
  CWL: 'Changes_When_Lowercased',
  Changes_When_NFKC_Casefolded: 'Changes_When_NFKC_Casefolded',
  CWKCF: 'Changes_When_NFKC_Casefolded',
  Changes_When_Titlecased: 'Changes_When_Titlecased',
  CWT: 'Changes_When_Titlecased',
  Changes_When_Uppercased: 'Changes_When_Uppercased',
  CWU: 'Changes_When_Uppercased',
  Dash: 'Dash',
  Default_Ignorable_Code_Point: 'Default_Ignorable_Code_Point',
  DI: 'Default_Ignorable_Code_Point',
  Deprecated: 'Deprecated',
  Dep: 'Deprecated',
  Diacritic: 'Diacritic',
  Dia: 'Diacritic',
  Emoji: 'Emoji',
  Emoji_Component: 'Emoji_Component',
  EComp: 'Emoji_Component',
  Emoji_Modifier: 'Emoji_Modifier',
  EMod: 'Emoji_Modifier',
  Emoji_Modifier_Base: 'Emoji_Modifier_Base',
  EBase: 'Emoji_Modifier_Base',
  Emoji_Presentation: 'Emoji_Presentation',
  EPres: 'Emoji_Presentation',
  Extended_Pictographic: 'Extended_Pictographic',
  ExtPict: 'Extended_Pictographic',
  Extender: 'Extender',
  Ext: 'Extender',
  Grapheme_Base: 'Grapheme_Base',
  Gr_Base: 'Grapheme_Base',
  Grapheme_Extend: 'Grapheme_Extend',
  Gr_Ext: 'Grapheme_Extend',
  Hex_Digit: 'Hex_Digit',
  Hex: 'Hex_Digit',
  IDS_Binary_Operator: 'IDS_Binary_Operator',
  IDSB: 'IDS_Binary_Operator',
  IDS_Trinary_Operator: 'IDS_Trinary_Operator',
  IDST: 'IDS_Trinary_Operator',
  ID_Continue: 'ID_Continue',
  IDC: 'ID_Continue',
  ID_Start: 'ID_Start',
  IDS: 'ID_Start',
  Ideographic: 'Ideographic',
  Ideo: 'Ideographic',
  Join_Control: 'Join_Control',
  Join_C: 'Join_Control',
  Logical_Order_Exception: 'Logical_Order_Exception',
  LOE: 'Logical_Order_Exception',
  Lowercase: 'Lowercase',
  Lower: 'Lowercase',
  Math: 'Math',
  Noncharacter_Code_Point: 'Noncharacter_Code_Point',
  NChar: 'Noncharacter_Code_Point',
  Pattern_Syntax: 'Pattern_Syntax',
  Pat_Syn: 'Pattern_Syntax',
  Pattern_White_Space: 'Pattern_White_Space',
  Pat_WS: 'Pattern_White_Space',
  Quotation_Mark: 'Quotation_Mark',
  QMark: 'Quotation_Mark',
  Radical: 'Radical',
  Regional_Indicator: 'Regional_Indicator',
  RI: 'Regional_Indicator',
  Sentence_Terminal: 'Sentence_Terminal',
  STerm: 'Sentence_Terminal',
  Soft_Dotted: 'Soft_Dotted',
  SD: 'Soft_Dotted',
  Terminal_Punctuation: 'Terminal_Punctuation',
  Term: 'Terminal_Punctuation',
  Unified_Ideograph: 'Unified_Ideograph',
  UIdeo: 'Unified_Ideograph',
  Uppercase: 'Uppercase',
  Upper: 'Uppercase',
  Variation_Selector: 'Variation_Selector',
  VS: 'Variation_Selector',
  White_Space: 'White_Space',
  space: 'White_Space',
  XID_Continue: 'XID_Continue',
  XIDC: 'XID_Continue',
  XID_Start: 'XID_Start',
  XIDS: 'XID_Start',
} as const;
Object.setPrototypeOf(BinaryUnicodeProperties, null);

// #table-unicode-general-category-values
export const UnicodeGeneralCategoryValues: Readonly<Record<string, string>> = {
  Cased_Letter: 'Cased_Letter',
  LC: 'Cased_Letter',
  Close_Punctuation: 'Close_Punctuation',
  Pe: 'Close_Punctuation',
  Connector_Punctuation: 'Connector_Punctuation',
  Pc: 'Connector_Punctuation',
  Control: 'Control',
  Cc: 'Control',
  cntrl: 'Control',
  Currency_Symbol: 'Currency_Symbol',
  Sc: 'Currency_Symbol',
  Dash_Punctuation: 'Dash_Punctuation',
  Pd: 'Dash_Punctuation',
  Decimal_Number: 'Decimal_Number',
  Nd: 'Decimal_Number',
  digit: 'Decimal_Number',
  Enclosing_Mark: 'Enclosing_Mark',
  Me: 'Enclosing_Mark',
  Final_Punctuation: 'Final_Punctuation',
  Pf: 'Final_Punctuation',
  Format: 'Format',
  Cf: 'Format',
  Initial_Punctuation: 'Initial_Punctuation',
  Pi: 'Initial_Punctuation',
  Letter: 'Letter',
  L: 'Letter',
  Letter_Number: 'Letter_Number',
  Nl: 'Letter_Number',
  Line_Separator: 'Line_Separator',
  Zl: 'Line_Separator',
  Lowercase_Letter: 'Lowercase_Letter',
  Ll: 'Lowercase_Letter',
  Mark: 'Mark',
  M: 'Mark',
  Combining_Mark: 'Mark',
  Math_Symbol: 'Math_Symbol',
  Sm: 'Math_Symbol',
  Modifier_Letter: 'Modifier_Letter',
  Lm: 'Modifier_Letter',
  Modifier_Symbol: 'Modifier_Symbol',
  Sk: 'Modifier_Symbol',
  Nonspacing_Mark: 'Nonspacing_Mark',
  Mn: 'Nonspacing_Mark',
  Number: 'Number',
  N: 'Number',
  Open_Punctuation: 'Open_Punctuation',
  Ps: 'Open_Punctuation',
  Other: 'Other',
  C: 'Other',
  Other_Letter: 'Other_Letter',
  Lo: 'Other_Letter',
  Other_Number: 'Other_Number',
  No: 'Other_Number',
  Other_Punctuation: 'Other_Punctuation',
  Po: 'Other_Punctuation',
  Other_Symbol: 'Other_Symbol',
  So: 'Other_Symbol',
  Paragraph_Separator: 'Paragraph_Separator',
  Zp: 'Paragraph_Separator',
  Private_Use: 'Private_Use',
  Co: 'Private_Use',
  Punctuation: 'Punctuation',
  P: 'Punctuation',
  punct: 'Punctuation',
  Separator: 'Separator',
  Z: 'Separator',
  Space_Separator: 'Space_Separator',
  Zs: 'Space_Separator',
  Spacing_Mark: 'Spacing_Mark',
  Mc: 'Spacing_Mark',
  Surrogate: 'Surrogate',
  Cs: 'Surrogate',
  Symbol: 'Symbol',
  S: 'Symbol',
  Titlecase_Letter: 'Titlecase_Letter',
  Lt: 'Titlecase_Letter',
  Unassigned: 'Unassigned',
  Cn: 'Unassigned',
  Uppercase_Letter: 'Uppercase_Letter',
  Lu: 'Uppercase_Letter',
};
Object.setPrototypeOf(UnicodeGeneralCategoryValues, null);

// #table-unicode-script-values
export const UnicodeScriptValues: Readonly<Record<string, string>> = {
  Adlam: 'Adlam',
  Adlm: 'Adlam',
  Ahom: 'Ahom',
  Anatolian_Hieroglyphs: 'Anatolian_Hieroglyphs',
  Hluw: 'Anatolian_Hieroglyphs',
  Arabic: 'Arabic',
  Arab: 'Arabic',
  Armenian: 'Armenian',
  Armn: 'Armenian',
  Avestan: 'Avestan',
  Avst: 'Avestan',
  Balinese: 'Balinese',
  Bali: 'Balinese',
  Bamum: 'Bamum',
  Bamu: 'Bamum',
  Bassa_Vah: 'Bassa_Vah',
  Bass: 'Bassa_Vah',
  Batak: 'Batak',
  Batk: 'Batak',
  Bengali: 'Bengali',
  Beng: 'Bengali',
  Bhaiksuki: 'Bhaiksuki',
  Bhks: 'Bhaiksuki',
  Bopomofo: 'Bopomofo',
  Bopo: 'Bopomofo',
  Brahmi: 'Brahmi',
  Brah: 'Brahmi',
  Braille: 'Braille',
  Brai: 'Braille',
  Buginese: 'Buginese',
  Bugi: 'Buginese',
  Buhid: 'Buhid',
  Buhd: 'Buhid',
  Canadian_Aboriginal: 'Canadian_Aboriginal',
  Cans: 'Canadian_Aboriginal',
  Carian: 'Carian',
  Cari: 'Carian',
  Caucasian_Albanian: 'Caucasian_Albanian',
  Aghb: 'Caucasian_Albanian',
  Chakma: 'Chakma',
  Cakm: 'Chakma',
  Cham: 'Cham',
  Chorasmian: 'Chorasmian',
  Chrs: 'Chorasmian',
  Cherokee: 'Cherokee',
  Cher: 'Cherokee',
  Common: 'Common',
  Zyyy: 'Common',
  Coptic: 'Coptic',
  Copt: 'Coptic',
  Qaac: 'Coptic',
  Cuneiform: 'Cuneiform',
  Xsux: 'Cuneiform',
  Cypriot: 'Cypriot',
  Cprt: 'Cypriot',
  Cyrillic: 'Cyrillic',
  Cyrl: 'Cyrillic',
  Deseret: 'Deseret',
  Dsrt: 'Deseret',
  Devanagari: 'Devanagari',
  Deva: 'Devanagari',
  Dives_Akuru: 'Dives_Akuru',
  Diak: 'Dives_Akuru',
  Dogra: 'Dogra',
  Dogr: 'Dogra',
  Duployan: 'Duployan',
  Dupl: 'Duployan',
  Egyptian_Hieroglyphs: 'Egyptian_Hieroglyphs',
  Egyp: 'Egyptian_Hieroglyphs',
  Elbasan: 'Elbasan',
  Elba: 'Elbasan',
  Elymaic: 'Elymaic',
  Elym: 'Elymaic',
  Ethiopic: 'Ethiopic',
  Ethi: 'Ethiopic',
  Georgian: 'Georgian',
  Geor: 'Georgian',
  Glagolitic: 'Glagolitic',
  Glag: 'Glagolitic',
  Gothic: 'Gothic',
  Goth: 'Gothic',
  Grantha: 'Grantha',
  Gran: 'Grantha',
  Greek: 'Greek',
  Grek: 'Greek',
  Gujarati: 'Gujarati',
  Gujr: 'Gujarati',
  Gunjala_Gondi: 'Gunjala_Gondi',
  Gong: 'Gunjala_Gondi',
  Gurmukhi: 'Gurmukhi',
  Guru: 'Gurmukhi',
  Han: 'Han',
  Hani: 'Han',
  Hangul: 'Hangul',
  Hang: 'Hangul',
  Hanifi_Rohingya: 'Hanifi_Rohingya',
  Rohg: 'Hanifi_Rohingya',
  Hanunoo: 'Hanunoo',
  Hano: 'Hanunoo',
  Hatran: 'Hatran',
  Hatr: 'Hatran',
  Hebrew: 'Hebrew',
  Hebr: 'Hebrew',
  Hiragana: 'Hiragana',
  Hira: 'Hiragana',
  Imperial_Aramaic: 'Imperial_Aramaic',
  Armi: 'Imperial_Aramaic',
  Inherited: 'Inherited',
  Zinh: 'Inherited',
  Qaai: 'Inherited',
  Inscriptional_Pahlavi: 'Inscriptional_Pahlavi',
  Phli: 'Inscriptional_Pahlavi',
  Inscriptional_Parthian: 'Inscriptional_Parthian',
  Prti: 'Inscriptional_Parthian',
  Javanese: 'Javanese',
  Java: 'Javanese',
  Kaithi: 'Kaithi',
  Kthi: 'Kaithi',
  Kannada: 'Kannada',
  Knda: 'Kannada',
  Katakana: 'Katakana',
  Kana: 'Katakana',
  Kayah_Li: 'Kayah_Li',
  Kali: 'Kayah_Li',
  Kharoshthi: 'Kharoshthi',
  Khar: 'Kharoshthi',
  Khitan_Small_Script: 'Khitan_Small_Script',
  Kits: 'Khitan_Small_Script',
  Khmer: 'Khmer',
  Khmr: 'Khmer',
  Khojki: 'Khojki',
  Khoj: 'Khojki',
  Khudawadi: 'Khudawadi',
  Sind: 'Khudawadi',
  Lao: 'Lao',
  Laoo: 'Lao',
  Latin: 'Latin',
  Latn: 'Latin',
  Lepcha: 'Lepcha',
  Lepc: 'Lepcha',
  Limbu: 'Limbu',
  Limb: 'Limbu',
  Linear_A: 'Linear_A',
  Lina: 'Linear_A',
  Linear_B: 'Linear_B',
  Linb: 'Linear_B',
  Lisu: 'Lisu',
  Lycian: 'Lycian',
  Lyci: 'Lycian',
  Lydian: 'Lydian',
  Lydi: 'Lydian',
  Mahajani: 'Mahajani',
  Mahj: 'Mahajani',
  Makasar: 'Makasar',
  Maka: 'Makasar',
  Malayalam: 'Malayalam',
  Mlym: 'Malayalam',
  Mandaic: 'Mandaic',
  Mand: 'Mandaic',
  Manichaean: 'Manichaean',
  Mani: 'Manichaean',
  Marchen: 'Marchen',
  Marc: 'Marchen',
  Medefaidrin: 'Medefaidrin',
  Medf: 'Medefaidrin',
  Masaram_Gondi: 'Masaram_Gondi',
  Gonm: 'Masaram_Gondi',
  Meetei_Mayek: 'Meetei_Mayek',
  Mtei: 'Meetei_Mayek',
  Mende_Kikakui: 'Mende_Kikakui',
  Mend: 'Mende_Kikakui',
  Meroitic_Cursive: 'Meroitic_Cursive',
  Merc: 'Meroitic_Cursive',
  Meroitic_Hieroglyphs: 'Meroitic_Hieroglyphs',
  Mero: 'Meroitic_Hieroglyphs',
  Miao: 'Miao',
  Plrd: 'Miao',
  Modi: 'Modi',
  Mongolian: 'Mongolian',
  Mong: 'Mongolian',
  Mro: 'Mro',
  Mroo: 'Mro',
  Multani: 'Multani',
  Mult: 'Multani',
  Myanmar: 'Myanmar',
  Mymr: 'Myanmar',
  Nabataean: 'Nabataean',
  Nbat: 'Nabataean',
  Nandinagari: 'Nandinagari',
  Nand: 'Nandinagari',
  New_Tai_Lue: 'New_Tai_Lue',
  Talu: 'New_Tai_Lue',
  Newa: 'Newa',
  Nko: 'Nko',
  Nkoo: 'Nko',
  Nushu: 'Nushu',
  Nshu: 'Nushu',
  Nyiakeng_Puachue_Hmong: 'Nyiakeng_Puachue_Hmong',
  Hmnp: 'Nyiakeng_Puachue_Hmong',
  Ogham: 'Ogham',
  Ogam: 'Ogham',
  Ol_Chiki: 'Ol_Chiki',
  Olck: 'Ol_Chiki',
  Old_Hungarian: 'Old_Hungarian',
  Hung: 'Old_Hungarian',
  Old_Italic: 'Old_Italic',
  Ital: 'Old_Italic',
  Old_North_Arabian: 'Old_North_Arabian',
  Narb: 'Old_North_Arabian',
  Old_Permic: 'Old_Permic',
  Perm: 'Old_Permic',
  Old_Persian: 'Old_Persian',
  Xpeo: 'Old_Persian',
  Old_Sogdian: 'Old_Sogdian',
  Sogo: 'Old_Sogdian',
  Old_South_Arabian: 'Old_South_Arabian',
  Sarb: 'Old_South_Arabian',
  Old_Turkic: 'Old_Turkic',
  Orkh: 'Old_Turkic',
  Oriya: 'Oriya',
  Orya: 'Oriya',
  Osage: 'Osage',
  Osge: 'Osage',
  Osmanya: 'Osmanya',
  Osma: 'Osmanya',
  Pahawh_Hmong: 'Pahawh_Hmong',
  Hmng: 'Pahawh_Hmong',
  Palmyrene: 'Palmyrene',
  Palm: 'Palmyrene',
  Pau_Cin_Hau: 'Pau_Cin_Hau',
  Pauc: 'Pau_Cin_Hau',
  Phags_Pa: 'Phags_Pa',
  Phag: 'Phags_Pa',
  Phoenician: 'Phoenician',
  Phnx: 'Phoenician',
  Psalter_Pahlavi: 'Psalter_Pahlavi',
  Phlp: 'Psalter_Pahlavi',
  Rejang: 'Rejang',
  Rjng: 'Rejang',
  Runic: 'Runic',
  Runr: 'Runic',
  Samaritan: 'Samaritan',
  Samr: 'Samaritan',
  Saurashtra: 'Saurashtra',
  Saur: 'Saurashtra',
  Sharada: 'Sharada',
  Shrd: 'Sharada',
  Shavian: 'Shavian',
  Shaw: 'Shavian',
  Siddham: 'Siddham',
  Sidd: 'Siddham',
  SignWriting: 'SignWriting',
  Sgnw: 'SignWriting',
  Sinhala: 'Sinhala',
  Sinh: 'Sinhala',
  Sogdian: 'Sogdian',
  Sogd: 'Sogdian',
  Sora_Sompeng: 'Sora_Sompeng',
  Sora: 'Sora_Sompeng',
  Soyombo: 'Soyombo',
  Soyo: 'Soyombo',
  Sundanese: 'Sundanese',
  Sund: 'Sundanese',
  Syloti_Nagri: 'Syloti_Nagri',
  Sylo: 'Syloti_Nagri',
  Syriac: 'Syriac',
  Syrc: 'Syriac',
  Tagalog: 'Tagalog',
  Tglg: 'Tagalog',
  Tagbanwa: 'Tagbanwa',
  Tagb: 'Tagbanwa',
  Tai_Le: 'Tai_Le',
  Tale: 'Tai_Le',
  Tai_Tham: 'Tai_Tham',
  Lana: 'Tai_Tham',
  Tai_Viet: 'Tai_Viet',
  Tavt: 'Tai_Viet',
  Takri: 'Takri',
  Takr: 'Takri',
  Tamil: 'Tamil',
  Taml: 'Tamil',
  Tangut: 'Tangut',
  Tang: 'Tangut',
  Telugu: 'Telugu',
  Telu: 'Telugu',
  Thaana: 'Thaana',
  Thaa: 'Thaana',
  Thai: 'Thai',
  Tibetan: 'Tibetan',
  Tibt: 'Tibetan',
  Tifinagh: 'Tifinagh',
  Tfng: 'Tifinagh',
  Tirhuta: 'Tirhuta',
  Tirh: 'Tirhuta',
  Ugaritic: 'Ugaritic',
  Ugar: 'Ugaritic',
  Vai: 'Vai',
  Vaii: 'Vai',
  Wancho: 'Wancho',
  Wcho: 'Wancho',
  Warang_Citi: 'Warang_Citi',
  Wara: 'Warang_Citi',
  Yezidi: 'Yezidi',
  Yezi: 'Yezidi',
  Yi: 'Yi',
  Yiii: 'Yi',
  Zanabazar_Square: 'Zanabazar_Square',
  Zanb: 'Zanabazar_Square',
} as const;
Object.setPrototypeOf(UnicodeScriptValues, null);

/** https://tc39.es/ecma262/#sec-runtime-semantics-unicodematchproperty-p */
export function UnicodeMatchProperty(p: string): string {
  // 1. Assert: p is a List of Unicode code points that is identical to a List of Unicode code points that is a Unicode property name or property alias listed in the “Property name and aliases” column of Table 55 or Table 56.
  Assert(p in NonbinaryUnicodeProperties || p in BinaryUnicodeProperties);
  type p = keyof typeof NonbinaryUnicodeProperties & keyof typeof BinaryUnicodeProperties;
  // 2. Let c be the canonical property name of p as given in the “Canonical property name” column of the corresponding row.
  const c = NonbinaryUnicodeProperties[p as p] || BinaryUnicodeProperties[p as p];
  // 3. Return the List of Unicode code points of c.
  return c;
}

/** https://tc39.es/ecma262/#sec-runtime-semantics-unicodematchpropertyvalue-p-v */
export function UnicodeMatchPropertyValue(p: string, v: string) {
  // 1. Assert: p is a List of Unicode code points that is identical to a List of Unicode code points that is a canonical, unaliased Unicode property name listed in the “Canonical property name” column of Table 55.
  Assert(p in NonbinaryUnicodeProperties);
  // 2. Assert: v is a List of Unicode code points that is identical to a List of Unicode code points that is a property value or property value alias for Unicode property p listed in the “Property value and aliases” column of Table 57 or Table 58.
  // Assert(v in UnicodeGeneralCategoryValues || v in UnicodeScriptValues);
  // 3. Let value be the canonical property value of v as given in the “Canonical property value” column of the corresponding row.
  const value = UnicodeGeneralCategoryValues[v] || UnicodeScriptValues[v];
  // 4. Return the List of Unicode code points of value.
  return value;
}

const expandedSets = new Map<string, Set<number>>();
export function getUnicodePropertyValueSet(property: string, value?: string) {
  const path = value ? `${property}/${value}` : `Binary_Property/${property}`;
  if (!expandedSets.has(path)) {
    const set = new Set<number>();
    (UnicodeSets as Record<string, number[][]>)[path].forEach(([from, to]) => {
      for (let i = from; i <= to; i += 1) {
        set.add(i);
      }
    });
    expandedSets.set(path, set);
  }
  return expandedSets.get(path)!;
}
