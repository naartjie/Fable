import { IComparable, combineHashCodes, compare, compareArrays, equalArrays, equals, sameConstructor, numberHash, structuralHash } from "./Util.js";

export function seqToString<T>(self: Iterable<T>): string {
  let count = 0;
  let str = "[";
  for (const x of self) {
    if (count === 0) {
      str += toString(x);
    } else if (count === 100) {
      str += "; ...";
      break;
    } else {
      str += "; " + toString(x);
    }
    count++;
  }
  return str + "]";
}

export function toString(x: any, callStack = 0): string {
  if (x != null && typeof x === "object") {
    if (typeof x.ToString === "function") {
      return x.ToString();
    } else if (Symbol.iterator in x) {
      return seqToString(x);
    } else { // TODO: Date?
      const cons = Object.getPrototypeOf(x).constructor;
      return cons === Object && callStack < 10
        // Same format as recordToString
        ? "{ " + Object.entries(x).map(([k, v]) => k + " = " + toString(v, callStack + 1)).join("\n  ") + " }"
        : cons.name;
    }
  }
  return String(x);
}

function compareList<T>(self: List<T>, other: List<T>): number {
  if (self === other) {
    return 0;
  } else {
    if (other == null) {
      return -1;
    }
    while (self.tail != null) {
      if (other.tail == null) { return 1; }
      const res = compare(self.head, other.head);
      if (res !== 0) { return res; }
      self = self.tail;
      other = other.tail;
    }
    return other.tail == null ? 0 : -1;
  }
}

export class List<T> implements IComparable<List<T>>, Iterable<T> {
  public head: T;
  public tail?: List<T>;

  constructor(head?: T, tail?: List<T>) {
    this.head = head as T;
    this.tail = tail;
  }

  public [Symbol.iterator](): Iterator<T> {
    let cur: List<T> | undefined = this;
    return {
      next: (): IteratorResult<T> => {
        const value = cur?.head as T;
        const done = cur?.tail == null;
        cur = cur?.tail;
        return { done, value };
      },
    };
  }

  public toJSON() { return Array.from(this); }
  public toString() { return this.ToString(); }
  public ToString() { return seqToString(this); }
  public GetHashCode() { return combineHashCodes(Array.from(this).map(structuralHash)); }
  public Equals(other: List<T>): boolean { return compareList(this, other) === 0; }
  public CompareTo(other: List<T>): number { return compareList(this, other); }
}

export abstract class Union implements IComparable<Union> {
  public tag!: number;
  public fields!: any[];
  abstract cases(): string[];

  public get name() {
    return this.cases()[this.tag];
  }

  public toJSON() {
    return this.fields.length === 0 ? this.name : [this.name].concat(this.fields);
  };

  public toString() {
    return this.ToString();
  }

  public ToString() {
    if (this.fields.length === 0) {
      return this.name;
    } else {
      let fields = "";
      let withParens = true;
      if (this.fields.length === 1) {
        const field = toString(this.fields[0]);
        withParens = field.indexOf(" ") >= 0;
        fields = field;
      }
      else {
        fields = this.fields.map((x: any) => toString(x)).join(", ");
      }
      return this.name + (withParens ? " (" : " ") + fields + (withParens ? ")" : "");
    }
  }

  public GetHashCode() {
    const hashes = this.fields.map((x: any) => structuralHash(x));
    hashes.splice(0, 0, numberHash(this.tag));
    return combineHashCodes(hashes);
  }

  public Equals(other: Union) {
    if (this === other) {
      return true;
    } else if (!sameConstructor(this, other)) {
      return false;
    } else if (this.tag === other.tag) {
      return equalArrays(this.fields, other.fields);
    } else {
      return false;
    }
  }

  public CompareTo(other: Union) {
    if (this === other) {
      return 0;
    } else if (!sameConstructor(this, other)) {
      return -1;
    } else if (this.tag === other.tag) {
      return compareArrays(this.fields, other.fields);
    } else {
      return this.tag < other.tag ? -1 : 1;
    }
  }
}

function recordToJSON<T>(self: T) {
  const o: any = {};
  const keys = Object.keys(self);
  for (let i = 0; i < keys.length; i++) {
    o[keys[i]] = (self as any)[keys[i]];
  }
  return o;
}

function recordToString<T>(self: T) {
  return "{ " + Object.entries(self).map(([k, v]) => k + " = " + toString(v)).join("\n  ") + " }";
}

function recordGetHashCode<T>(self: T) {
  const hashes = Object.values(self).map((v) => structuralHash(v));
  return combineHashCodes(hashes);
}

function recordEquals<T>(self: T, other: T) {
  if (self === other) {
    return true;
  } else if (!sameConstructor(self, other)) {
    return false;
  } else {
    const thisNames = Object.keys(self);
    for (let i = 0; i < thisNames.length; i++) {
      if (!equals((self as any)[thisNames[i]], (other as any)[thisNames[i]])) {
        return false;
      }
    }
    return true;
  }
}

function recordCompareTo<T>(self: T, other: T) {
  if (self === other) {
    return 0;
  } else if (!sameConstructor(self, other)) {
    return -1;
  } else {
    const thisNames = Object.keys(self);
    for (let i = 0; i < thisNames.length; i++) {
      const result = compare((self as any)[thisNames[i]], (other as any)[thisNames[i]]);
      if (result !== 0) {
        return result;
      }
    }
    return 0;
  }
}

export abstract class Record implements IComparable<Record> {
  toJSON() { return recordToJSON(this); }
  toString() { return this.ToString(); }
  ToString() { return recordToString(this); }
  GetHashCode() { return recordGetHashCode(this); }
  Equals(other: Record) { return recordEquals(this, other); }
  CompareTo(other: Record) { return recordCompareTo(this, other); }
}

export class FSharpRef<T> {
  private getter: () => T;
  private setter: (v: T) => void;

  get contents() {
    return this.getter();
  }

  set contents(v) {
    this.setter(v)
  }

  constructor(contentsOrGetter: T | (() => T), setter?: (v: T) => void) {
    if (typeof setter === "function") {
      this.getter = contentsOrGetter as () => T;
      this.setter = setter
    } else {
      this.getter = () => contentsOrGetter as T;
      this.setter = (v) => { contentsOrGetter = v };
    }
  }
}

// EXCEPTIONS

// Exception is intentionally not derived from Error, for performance reasons (see #2160)
export class Exception {
  constructor(public message?: string) { }
}

export function isException(x: any) {
  return x instanceof Exception || x instanceof Error;
}

export abstract class FSharpException extends Exception implements IComparable<FSharpException> {
  toJSON() { return recordToJSON(this); }
  toString() { return this.ToString(); }
  ToString() { return recordToString(this); }
  GetHashCode() { return recordGetHashCode(this); }
  Equals(other: FSharpException) { return recordEquals(this, other); }
  CompareTo(other: FSharpException) { return recordCompareTo(this, other); }
}

export class MatchFailureException extends FSharpException {
  public arg1: string;
  public arg2: number;
  public arg3: number;
  public message: string;

  constructor(arg1: string, arg2: number, arg3: number) {
    super();
    this.arg1 = arg1;
    this.arg2 = arg2 | 0;
    this.arg3 = arg3 | 0;
    this.message = "The match cases were incomplete";
  }
}

export class Attribute {
}
