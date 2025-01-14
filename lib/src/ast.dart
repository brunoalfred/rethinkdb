part of rethinkdb;

const defaultNestingDepth = 20;

List buildInvocationParams(List<dynamic> positionalArguments,
    [List<String>? optionsNames]) {
  var argsList = [];
  argsList.addAll(positionalArguments);
  Map? options = {};
  if (argsList.length > 1 && argsList.last is Map) {
    if (optionsNames == null) {
      options = argsList.removeLast();
    } else {
      Map lastArgument = argsList.last;
      var isOptions = true;
      lastArgument.forEach((key, _) {
        if (!optionsNames.contains(key)) {
          isOptions = false;
        }
      });
      if (isOptions) {
        options = argsList.removeLast();
      }
    }
  }
  var invocationParams = [argsList];
  if (options!.isNotEmpty) {
    invocationParams.add(options);
  }
  return invocationParams;
}

// TODO: handle index.
// TODO: handle multi.
class GroupFunction {
  final RqlQuery? _rqlQuery;

  GroupFunction([this._rqlQuery]);

  Group call(args) {
    if (args is List) {
      return Group(_rqlQuery, args, null);
    } else {
      return Group(_rqlQuery, [args], null);
    }
  }

  @override
  dynamic noSuchMethod(Invocation invocation) {
    var positionalArguments = [];
    positionalArguments.addAll(invocation.positionalArguments);
    var invocationParams =
        buildInvocationParams(positionalArguments, ['index', 'multi']);
    return Group(_rqlQuery, invocationParams[0],
        invocationParams.length == 2 ? invocationParams[1] : null);
  }
}

class HasFieldsFunction {
  final RqlQuery? _rqlQuery;

  HasFieldsFunction([this._rqlQuery]);

  HasFields call(items) {
    return HasFields(_rqlQuery, items);
  }

  @override
  dynamic noSuchMethod(Invocation invocation) {
    var positionalArguments = [];
    positionalArguments.addAll(invocation.positionalArguments);
    return HasFields(_rqlQuery, buildInvocationParams(positionalArguments));
  }
}

class MergeFunction {
  final RqlQuery? _rqlQuery;

  MergeFunction([this._rqlQuery]);

  Merge call(obj) {
    return Merge([_rqlQuery, obj]);
  }

  @override
  dynamic noSuchMethod(Invocation invocation) {
    var positionalArguments = [];
    positionalArguments.add(_rqlQuery);
    positionalArguments.addAll(invocation.positionalArguments);
    return Merge(positionalArguments);
  }
}

class PluckFunction {
  final RqlQuery? _rqlQuery;

  PluckFunction([this._rqlQuery]);

  Pluck call(args) {
    return Pluck(_rqlQuery!._listify(args, _rqlQuery));
  }

  @override
  dynamic noSuchMethod(Invocation invocation) {
    var positionalArguments = [];
    positionalArguments.addAll(invocation.positionalArguments);
    return Pluck(_rqlQuery!
        ._listify(buildInvocationParams(positionalArguments), _rqlQuery));
  }
}

// TODO: handle interleave.
class UnionFunction {
  final RqlQuery? _rqlQuery;

  UnionFunction([this._rqlQuery]);

  Union call(sequence) {
    return Union(_rqlQuery, [sequence]);
  }

  @override
  dynamic noSuchMethod(Invocation invocation) {
    var positionalArguments = [];
    positionalArguments.addAll(invocation.positionalArguments);
    var invocationParams =
        buildInvocationParams(positionalArguments, ['interleave']);
    if (invocationParams.length == 2) {
      return Union(_rqlQuery, [invocationParams[0], invocationParams[1]]);
    } else {
      return Union(_rqlQuery, invocationParams[0]);
    }
  }
}

class WithoutFunction {
  final RqlQuery? _rqlQuery;

  WithoutFunction([this._rqlQuery]);

  Without call(items) {
    return Without(_rqlQuery!._listify(items, _rqlQuery));
  }

  @override
  dynamic noSuchMethod(Invocation invocation) {
    var positionalArguments = [];
    positionalArguments.addAll(invocation.positionalArguments);
    return Without(_rqlQuery!
        ._listify(buildInvocationParams(positionalArguments), _rqlQuery));
  }
}

class WithFieldsFunction {
  final RqlQuery? _rqlQuery;

  WithFieldsFunction([this._rqlQuery]);

  WithFields call(items) {
    return WithFields(_rqlQuery, items);
  }

  @override
  dynamic noSuchMethod(Invocation invocation) {
    var positionalArguments = [];
    positionalArguments.addAll(invocation.positionalArguments);
    return WithFields(_rqlQuery, buildInvocationParams(positionalArguments));
  }
}

class RqlMapFunction {
  final RqlQuery _rqlQuery;

  RqlMapFunction(this._rqlQuery);

  call(mappingFunction) {
    if (mappingFunction is List) {
      mappingFunction.insert(0, _rqlQuery);
      var item = _rqlQuery._funcWrap(
          mappingFunction.removeLast(), mappingFunction.length);
      return RqlMap(mappingFunction, item);
    }
    return RqlMap([_rqlQuery], mappingFunction);
  }

  @override
  dynamic noSuchMethod(Invocation invocation) {
    var mappingFunction = List.from(invocation.positionalArguments);
    mappingFunction.insert(0, _rqlQuery);
    var item = _rqlQuery._funcWrap(
        mappingFunction.removeLast(), mappingFunction.length);
    return RqlMap(mappingFunction, item);
  }
}

class RqlQuery {
  p.Term_TermType? tt;

  List args = [];
  Map optargs = {};

  RqlQuery([List? args, Map? optargs]) {
    if (args != null) {
      args.forEach((e) {
        if (_checkIfOptions(e, tt)) {
          optargs ??= e;
        } else if (e != null) {
          this.args.add(_expr(e));
        }
      });
    }

    if (optargs != null) {
      optargs!.forEach((k, v) {
        if ((k == 'conflict') && (v is Function)) {
          this.optargs[k] = _expr(v, defaultNestingDepth, 3);
        } else {
          this.optargs[k] = _expr(v);
        }
      });
    }
  }

  _expr(val, [nestingDepth = defaultNestingDepth, argsCount]) {
    if (nestingDepth <= 0) {
      throw RqlDriverError('Nesting depth limit exceeded');
    }

    if (nestingDepth is int == false) {
      throw RqlDriverError('Second argument to `r.expr` must be a number.');
    }

    if (val is RqlQuery) {
      return val;
    } else if (val is List) {
      val.forEach((v) {
        v = _expr(v, nestingDepth - 1, argsCount);
      });

      return MakeArray(val);
    } else if (val is Map) {
      Map obj = {};

      val.forEach((k, v) {
        obj[k] = _expr(v, nestingDepth - 1, argsCount);
      });

      return MakeObj(obj);
    } else if (val is Function) {
      return Func(val, argsCount);
    } else if (val is DateTime) {
      return Time(Args([
        val.year,
        val.month,
        val.day,
        val.hour,
        val.minute,
        val.second,
        _formatTimeZoneOffset(val)
      ]));
    }
    return Datum(val);
  }

  String _formatTimeZoneOffset(DateTime val) {
    var tz = val.timeZoneOffset.inHours.toString();

    if (!val.timeZoneOffset.inHours.isNegative) {
      tz = '+$tz';
    }

    if (tz.length == 2) {
      tz = tz.replaceRange(0, 1, tz[0] + '0');
    }

    return tz;
  }

  Future run(Connection? c, [globalOptargs]) {
    if (c == null) {
      throw RqlDriverError('RqlQuery.run must be given a connection to run.');
    }

    return c._start(this, globalOptargs);
  }

  //since a term that may take multiple options can now be passed
  //one or two, we can't know if the final argument in a query
  //is actually an option or just another arg.  _check_if_options
  //checks if all of the keys in the object are in options
  _checkIfOptions(obj, p.Term_TermType? tt) {
    if (obj is Map == false) {
      return false;
    } else {
      var options = _RqlAllOptions(tt).options;

      return obj.keys.every(options.contains);
    }
  }

  build() {
    var res = [];
    if (tt != null) {
      res.add(tt!.value);
    }

    var argList = [];
    args.forEach((arg) {
      if (arg != null) {
        argList.add(arg.build());
      }
    });
    res.add(argList);

    if (optargs.isNotEmpty) {
      Map optArgsMap = {};
      optargs.forEach((k, v) {
        optArgsMap[k] = v.build();
      });
      res.add(optArgsMap);
    }
    return res;
  }

  _recursivelyConvertPseudotypes(obj, formatOpts) {
    if (obj is Map) {
      obj.forEach((k, v) {
        obj[k] = _recursivelyConvertPseudotypes(v, formatOpts);
      });
      obj = _convertPseudotype(obj, formatOpts);
    } else if (obj is List) {
      obj.forEach((e) {
        e = _recursivelyConvertPseudotypes(e, formatOpts);
      });
    }
    return obj;
  }

  _listify(args, [parg]) {
    if (args is List) {
      args.insert(0, parg);
      return args;
    } else {
      if (args != null) {
        if (parg != null) {
          return [parg, args];
        } else {
          return [args];
        }
      } else {
        return [];
      }
    }
  }

  bool _ivarScan(query) {
    if (!(query is RqlQuery)) {
      return false;
    }

    if (query is ImplicitVar) {
      return true;
    }
    if (query.args.any(_ivarScan)) {
      return true;
    }

    dynamic optArgKeys = query.optargs.values;

    if (optArgKeys.any(_ivarScan)) {
      return true;
    }
    return false;
  }

  // Called on arguments that should be functions
  _funcWrap(val, [argsCount]) {
    val = _expr(val, defaultNestingDepth, argsCount);
    if (_ivarScan(val)) {
      return Func((x) => val, argsCount);
    }
    return val;
  }

  _reqlTypeTimeToDatetime(Map obj) {
    if (obj['epoch_time'] == null) {
      throw RqlDriverError(
          'pseudo-type TIME object $obj does not have expected field "epoch_time".');
    } else {
      var s = obj['epoch_time'].toString();
      if (s.contains('.')) {
        List l = s.split('.');
        while (l[1].length < 3) {
          l[1] = l[1] + '0';
        }
        s = l.join('');
      } else {
        s += '000';
      }
      return DateTime.fromMillisecondsSinceEpoch(int.parse(s));
    }
  }

  _reqlTypeGroupedDataToObject(Map obj) {
    if (obj['data'] == null) {
      throw RqlDriverError(
          'pseudo-type GROUPED_DATA object $obj does not have the expected field "data".');
    }

    Map retObj = {};
    obj['data'].forEach((e) {
      retObj[e[0]] = e[1];
    });
    return retObj;
  }

  _convertPseudotype(Map obj, Map? formatOpts) {
    String? reqlType = obj['\$reql_type\$'];
    if (reqlType != null) {
      if (reqlType == 'TIME') {
        if (formatOpts == null || formatOpts.isEmpty) {
          formatOpts = {'time_format': 'native'};
        }
        String? timeFormat = formatOpts['time_format'];
        if (timeFormat != null || timeFormat == 'native') {
          // Convert to native dart DateTime
          return _reqlTypeTimeToDatetime(obj);
        } else if (timeFormat != 'raw') {
          throw RqlDriverError('Unknown time_format run option $timeFormat.');
        }
      } else if (reqlType == 'GROUPED_DATA') {
        if (formatOpts == null ||
            formatOpts.isEmpty ||
            formatOpts['group_format'] == 'native') {
          return _reqlTypeGroupedDataToObject(obj);
        } else if (formatOpts['group_format'] != 'raw') {
          throw RqlDriverError(
              "Unknown group_format run option ${formatOpts['group_format']}.");
        }
      } else if (reqlType == 'BINARY') {
        if (formatOpts == null || formatOpts['binary_format'] == 'native') {
          /// the official drivers decode the BASE64 string to binary data
          /// this driver currently has a bug with its [_reqlTypeBinaryToBytes]
          /// for some reason, when trying to convert the index function for
          /// `indexWait` commands, we get a FormatException.
          ///  so for the short term we will just return the BASE64 string
          ///  with a TODO to find out what is wrong and fix it.

          try {
            return _reqlTypeBinaryToBytes(obj);
          } on FormatException {
            return obj['data'];
          }
        } else {
          throw RqlDriverError(
              "Unknown binary_format run option: ${formatOpts["binary_format"]}");
        }
      } else if (reqlType == 'GEOMETRY') {
        obj.remove('\$reql_type\$');
        return obj;
      } else {
        throw RqlDriverError('Unknown pseudo-type $reqlType');
      }
    }

    return obj;
  }

  _reqlTypeBinaryToBytes(Map obj) {
    return base64.decode(obj['data']);
  }

  Update update(args, [options]) => Update(this, _funcWrap(args, 1), options);

  // Comparison operators
  dynamic get eq => EqFunction(this);

  dynamic get ne => NeFunction(this);

  dynamic get lt => LtFunction(this);

  dynamic get le => LeFunction(this);

  dynamic get gt => GtFunction(this);

  dynamic get ge => GeFunction(this);

  // Numeric operators
  Not not() => Not(this);

  dynamic get add => AddFunction(this);

  dynamic get sub => SubFunction(this);

  dynamic get mul => MulFunction(this);

  dynamic get div => DivFunction(this);

  Mod mod(other) => Mod(this, other);

  dynamic get and => AndFunction(this);

  dynamic get or => OrFunction(this);

  Contains contains(args) => Contains(this, _funcWrap(args, 1));

  dynamic get hasFields => HasFieldsFunction(this);

  dynamic get withFields => WithFieldsFunction(this);

  Keys keys() => Keys(this);

  Values values() => Values(this);

  Changes changes([Map? opts]) => Changes(this, opts);

  // Polymorphic object/sequence operations
  dynamic get pluck => PluckFunction(this);

  dynamic get without => WithoutFunction(this);

  FunCall rqlDo(arg, [expression]) {
    if (expression == null) {
      return FunCall(this, _funcWrap(arg, 1));
    } else {
      return FunCall(_listify(arg, this), _funcWrap(expression, arg.length));
    }
  }

  Default rqlDefault(args) => Default(this, args);

  Replace replace(expr, [options]) =>
      Replace(this, _funcWrap(expr, 1), options);

  Delete delete([options]) => Delete(this, options);

  // Rql type inspection
  coerceTo(String type) => CoerceTo(this, type);

  Ungroup ungroup() => Ungroup(this);

  TypeOf typeOf() => TypeOf(this);

  dynamic get merge => MergeFunction(this);

  Append append(val) => Append(this, val);

  Floor floor() => Floor(this);

  Ceil ceil() => Ceil(this);

  Round round() => Round(this);

  Prepend prepend(val) => Prepend(this, val);

  Difference difference(List ar) => Difference(this, ar);

  SetInsert setInsert(val) => SetInsert(this, val);

  SetUnion setUnion(ar) => SetUnion(this, ar);

  SetIntersection setIntersection(ar) => SetIntersection(this, ar);

  SetDifference setDifference(ar) => SetDifference(this, ar);

  GetField getField(index) => GetField(this, index);

  Nth nth(int index) => Nth(this, index);

  Match match(String regex) => Match(this, regex);

  Split split([seperator = ' ', maxSplits]) =>
      Split(this, seperator, maxSplits);

  Upcase upcase() => Upcase(this);

  Downcase downcase() => Downcase(this);

  IsEmpty isEmpty() => IsEmpty(this);

  Slice slice(int start, [end, Map? options]) =>
      Slice(this, start, end, options);

  Fold fold(base, function, [options]) => Fold(this, base, function, options);

  Skip skip(int i) => Skip(this, i);

  Limit limit(int i) => Limit(this, i);

  Reduce reduce(reductionFunction, [base]) =>
      Reduce(this, _funcWrap(reductionFunction, 2), base);

  Sum sum([args]) => Sum(this, args);

  Avg avg([args]) => Avg(this, args);

  Min min([args]) => Min(this, args);

  Max max([args]) => Max(this, args);

  dynamic get map => RqlMapFunction(this);

  Filter filter(expr, [options]) => Filter(this, _funcWrap(expr, 1), options);

  ConcatMap concatMap(mappingFunction) =>
      ConcatMap(this, _funcWrap(mappingFunction, 1));

  Get get(id) => Get(this, id);

  OrderBy orderBy(attrs, [index]) {
    if (attrs is Map && attrs.containsKey('index')) {
      index = attrs;
      attrs = [];

      index.forEach((k, ob) {
        if (ob is Asc || ob is Desc) {
          //do nothing
        } else {
          ob = _funcWrap(ob, 1);
        }
      });
    } else if (attrs is List) {
      if (index is Map == false && index != null) {
        attrs.add(index);
        index = null;
      }
      attrs.forEach((ob) {
        if (ob is Asc || ob is Desc) {
          //do nothing
        } else {
          ob = _funcWrap(ob, 1);
        }
      });
    } else {
      var tmp = [];
      tmp.add(attrs);
      if (index is Map == false && index != null) {
        tmp.add(index);
        index = null;
      }
      attrs = tmp;
    }

    return OrderBy(_listify(attrs, this), index);
  }

  operator +(other) => add(other);
  operator -(other) => sub(other);
  operator *(other) => mul(other);
  operator /(other) => div(other);
  // TODO see if we can still do this. != isn't assignable so maybe
  // it makes more sense not to do == anyway.
  //operator ==(other) => this.eq(other);
  operator <=(other) => le(other);
  operator >=(other) => ge(other);
  operator <(other) => lt(other);
  operator >(other) => gt(other);
  operator %(other) => mod(other);
  operator [](attr) => pluck(attr);

  Between between(lowerKey, [upperKey, options]) =>
      Between(this, lowerKey, upperKey, options);

  Distinct distinct() => Distinct(this);

  Count count([filter]) {
    if (filter == null) return Count(this);
    return Count(this, _funcWrap(filter, 1));
  }

  dynamic get union => UnionFunction(this);

  InnerJoin innerJoin(otherSequence, [predicate]) =>
      InnerJoin(this, otherSequence, predicate);

  OuterJoin outerJoin(otherSequence, [predicate]) =>
      OuterJoin(this, otherSequence, predicate);

  EqJoin eqJoin(leftAttr, [otherTable, options]) =>
      EqJoin(this, _funcWrap(leftAttr, 1), otherTable, options);

  Zip zip() => Zip(this);

  dynamic get group => GroupFunction(this);

  ForEach forEach(writeQuery) => ForEach(this, _funcWrap(writeQuery, 1));

  Info info() => Info(this);

  //Array only operations

  InsertAt insertAt(index, [value]) => InsertAt(this, index, value);

  SpliceAt spliceAt(index, [ar]) => SpliceAt(this, index, ar);

  DeleteAt deleteAt(index, [end]) => DeleteAt(this, index, end);

  ChangeAt changeAt(index, [value]) => ChangeAt(this, index, value);

  Sample sample(int i) => Sample(this, i);

  // Time support
  ToISO8601 toISO8601() => ToISO8601(this);

  ToEpochTime toEpochTime() => ToEpochTime(this);

  During during(start, [end, options]) => During(this, start, end, options);

  Date date() => Date(this);

  TimeOfDay timeOfDay() => TimeOfDay(this);

  Timezone timezone() => Timezone(this);

  Year year() => Year(this);

  Month month() => Month(this);

  Day day() => Day(this);

  DayOfWeek dayOfWeek() => DayOfWeek(this);

  DayOfYear dayOfYear() => DayOfYear(this);

  Hours hours() => Hours(this);

  Minutes minutes() => Minutes(this);

  Seconds seconds() => Seconds(this);

  InTimezone inTimezone(tz) => InTimezone(this, tz);

  Binary binary(data) => Binary(data);

  Distance distance(geo, [opts]) => Distance(this, geo, opts);

  Fill fill() => Fill(this);

  ToGeoJson toGeojson() => ToGeoJson(this);

  GetIntersecting getIntersecting(geo, Map options) =>
      GetIntersecting(this, geo, options);

  GetNearest getNearest(point, [Map? options]) =>
      GetNearest(this, point, options);

  Includes includes(geo) => Includes(this, geo);

  Intersects intersects(geo) => Intersects(this, geo);

  PolygonSub polygonSub(var poly) => PolygonSub(this, poly);

  Config config() => Config(this);

  Rebalance rebalance() => Rebalance(this);

  Reconfigure reconfigure(Map options) => Reconfigure(this, options);

  Status status() => Status(this);

  Wait wait([Map? options]) => Wait(this, options);

  call(attr) {
    return GetField(this, attr);
  }
}

//TODO write pretty compose functions
class RqlBoolOperQuery extends RqlQuery {
  RqlBoolOperQuery([List? args, Map? optargs]) : super(args, optargs);
}

class RqlBiOperQuery extends RqlQuery {
  RqlBiOperQuery([List? args, Map? optargs]) : super(args, optargs);
}

class RqlBiCompareOperQuery extends RqlBiOperQuery {
  RqlBiCompareOperQuery([List? args, Map? optargs]) : super(args, optargs);
}

class RqlTopLevelQuery extends RqlQuery {
  RqlTopLevelQuery([List? args, Map? optargs]) : super(args, optargs);
}

class RqlMethodQuery extends RqlQuery {
  RqlMethodQuery([List? args, Map? optargs]) : super(args, optargs);
}

class RqlBracketQuery extends RqlMethodQuery {
  RqlBracketQuery([List? args, Map? optargs]) : super(args, optargs);
}

class Datum extends RqlQuery {
  @override
  List args = [];
  @override
  Map optargs = {};
  var data;

  Datum(val) : super(null, null) {
    data = val;
  }

  @override
  build() {
    return data;
  }
}

class MakeArray extends RqlQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.MAKE_ARRAY;

  MakeArray(args) : super(args);
}

class MakeObj extends RqlQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.MAKE_OBJ;

  MakeObj(objDict) : super(null, objDict);

  @override
  build() {
    var res = {};
    optargs.forEach((k, v) {
      res[k is RqlQuery ? k.build() : k] = v is RqlQuery ? v.build() : v;
    });
    return res;
  }
}

class Var extends RqlQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.VAR;

  Var(args) : super([args]);

  @override
  call(arg) => GetField(this, arg);
}

class JavaScript extends RqlTopLevelQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.JAVASCRIPT;

  JavaScript(args, [optargs]) : super([args], optargs);
}

class Http extends RqlTopLevelQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.HTTP;

  Http(args, [optargs]) : super([args], optargs);
}

class UserError extends RqlTopLevelQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.ERROR;

  UserError(args, [optargs]) : super([args], optargs);
}

class Random extends RqlTopLevelQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.RANDOM;

  Random(optargs) : super(null, optargs ?? {});

  Random.leftBound(left, optargs) : super([left], optargs ?? {});

  Random.rightBound(left, right, optargs) : super([left, right], optargs ?? {});
}

class Changes extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.CHANGES;

  Changes([arg, opts]) : super([arg], opts);
}

class Fold extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.FOLD;

  Fold(seq, base, func, [opts]) : super([seq, base, func], opts);
}

class Grant extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.GRANT;

  Grant([scope, user, options]) : super([scope, user], options);
}

class Default extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.DEFAULT;

  Default(obj, value) : super([obj, value]);
}

class ImplicitVar extends RqlQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.IMPLICIT_VAR;

  ImplicitVar() : super();

  @override
  call(arg) => GetField(this, arg);
}

class Eq extends RqlBiCompareOperQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.EQ;

  Eq(numbers) : super(numbers);
}

class Ne extends RqlBiCompareOperQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.NE;

  Ne(numbers) : super(numbers);
}

class Lt extends RqlBiCompareOperQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.LT;

  Lt(numbers) : super(numbers);
}

class Le extends RqlBiCompareOperQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.LE;

  Le(numbers) : super(numbers);
}

class Gt extends RqlBiCompareOperQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.GT;

  Gt(numbers) : super(numbers);
}

class Ge extends RqlBiCompareOperQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.GE;

  Ge(numbers) : super(numbers);
}

class Not extends RqlQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.NOT;

  Not([args]) : super([args]);
}

class Add extends RqlBiOperQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.ADD;

  Add(objects) : super(objects);
}

class Sub extends RqlBiOperQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.SUB;

  Sub(numbers) : super(numbers);
}

class Mul extends RqlBiOperQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.MUL;

  Mul(numbers) : super(numbers);
}

class Div extends RqlBiOperQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.DIV;

  Div(numbers) : super(numbers);
}

class Mod extends RqlBiOperQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.MOD;

  Mod(modable, obj) : super([modable, obj]);
}

class Append extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.APPEND;

  Append(ar, val) : super([ar, val]);
}

class Floor extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.FLOOR;

  Floor(ar) : super([ar]);
}

class Ceil extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.CEIL;

  Ceil(ar) : super([ar]);
}

class Round extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.ROUND;

  Round(ar) : super([ar]);
}

class Prepend extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.PREPEND;

  Prepend(ar, val) : super([ar, val]);
}

class Difference extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.DIFFERENCE;

  Difference(diffable, ar) : super([diffable, ar]);
}

class SetInsert extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.SET_INSERT;

  SetInsert(ar, val) : super([ar, val]);
}

class SetUnion extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.SET_UNION;

  SetUnion(un, val) : super([un, val]);
}

class SetIntersection extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.SET_INTERSECTION;

  SetIntersection(inter, ar) : super([inter, ar]);
}

class SetDifference extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.SET_DIFFERENCE;

  SetDifference(diff, ar) : super([diff, ar]);
}

class Slice extends RqlBracketQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.SLICE;

  Slice(selection, int start, [end, Map? options])
      : super([selection, start, end], options);
}

class Skip extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.SKIP;

  Skip(selection, int number) : super([selection, number]);
}

class Limit extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.LIMIT;

  Limit(selection, int number) : super([selection, number]);
}

class GetField extends RqlBracketQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.BRACKET;

  GetField(obj, field) : super([obj, field]);
}

class Contains extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.CONTAINS;

  Contains(tbl, items) : super([tbl, items]);
}

class HasFields extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.HAS_FIELDS;

  HasFields(obj, items) : super([obj, items]);
}

class WithFields extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.WITH_FIELDS;

  WithFields(obj, fields) : super([obj, fields]);
}

class Keys extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.KEYS;

  Keys(obj) : super([obj]);
}

class Values extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.VALUES;

  Values(obj) : super([obj]);
}

class RqlObject extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.OBJECT;

  RqlObject(args) : super(args);
}

class Pluck extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.PLUCK;

  Pluck(items) : super(items);
}

class Without extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.WITHOUT;

  Without(items) : super(items);
}

class Merge extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.MERGE;

  Merge(objects) : super(objects);
}

class Between extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.BETWEEN;

  Between(tbl, lower, upper, [options]) : super([tbl, lower, upper], options);
}

class DB extends RqlTopLevelQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.DB;

  DB(String? dbName) : super([dbName]);

  TableList tableList() => TableList(this);

  TableCreate tableCreate(String tableName, [Map? options]) =>
      TableCreate.fromDB(this, tableName, options);

  TableDrop tableDrop(String tableName) => TableDrop.fromDB(this, tableName);

  Table table(String tableName, [Map? options]) =>
      Table.fromDB(this, tableName, options);

  Grant grant(String user, [Map? options]) => Grant(this, user, options);
}

class FunCall extends RqlQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.FUNCALL;

  FunCall(argslist, expression) : super() {
    var temp = [];
    temp.add(expression);
    int argsCount;
    if (argslist is List) {
      argsCount = argslist.length;
      temp.addAll(argslist);
    } else {
      argsCount = 1;
      temp.add(argslist);
    }

    args.addAll(temp.map((arg) {
      return _expr(arg, defaultNestingDepth, argsCount);
    }));
  }
}

class GetAllFunction extends RqlQuery {
  final Table _table;

  GetAllFunction(this._table);

  @override
  GetAll call(args, [options]) {
    if (options != null && options is Map == false) {
      args = _listify(args, _table);
      options = args.add(options);
      return GetAll(args, options);
    }
    return GetAll(_listify(args, _table), options);
  }

  @override
  dynamic noSuchMethod(Invocation invocation) {
    var argsList = [];
    argsList.addAll(invocation.positionalArguments);
    return Function.apply(call, [argsList]);
  }
}

class IndexStatusFunction extends RqlQuery {
  final Table _table;

  IndexStatusFunction(this._table);

  @override
  IndexStatus call([indexes]) {
    if (indexes == null) {
      return IndexStatus.all(_table);
    }
    return IndexStatus(_table, indexes);
  }

  @override
  dynamic noSuchMethod(Invocation invocation) {
    var argsList = [];
    argsList.addAll(invocation.positionalArguments);
    return Function.apply(call, [argsList]);
  }
}

class IndexWaitFunction extends RqlQuery {
  final Table _table;

  IndexWaitFunction(this._table);

  @override
  IndexWait call([indexes]) {
    if (indexes == null) {
      return IndexWait.all(_table);
    }
    return IndexWait(_table, indexes);
  }

  @override
  dynamic noSuchMethod(Invocation invocation) {
    var argsList = [];
    argsList.addAll(invocation.positionalArguments);
    return Function.apply(call, [argsList]);
  }
}

class Table extends RqlQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.TABLE;

  Table(String tableName, [Map? options]) : super([tableName], options);

  Table.fromDB(DB db, String tableName, [Map? options])
      : super([db, tableName], options);

  Insert insert(records, [options]) => Insert(this, records, options);

  Grant grant(user, [options]) => Grant(this, user, options);

  IndexList indexList() => IndexList(this);

  IndexCreate indexCreate(indexName, [indexFunction, Map? options]) {
    if (indexFunction == null && options == null) {
      return IndexCreate(this, indexName);
    } else if (indexFunction != null && indexFunction is Map) {
      return IndexCreate(this, indexName, indexFunction);
    }
    return IndexCreate.withIndexFunction(
        this, indexName, _funcWrap(indexFunction, 1), options);
  }

  IndexDrop indexDrop(indexName) => IndexDrop(this, indexName);

  IndexRename indexRename(oldName, newName, [Map? options]) =>
      IndexRename(this, oldName, newName, options);

  dynamic get indexStatus => IndexStatusFunction(this);

  dynamic get indexWait => IndexWaitFunction(this);

  @override
  Update update(args, [options]) => Update(this, _funcWrap(args, 1), options);

  Sync sync() => Sync(this);

  dynamic get getAll => GetAllFunction(this);

  @override
  InnerJoin innerJoin(otherSeq, [predicate]) =>
      InnerJoin(this, otherSeq, predicate);
}

class Get extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.GET;

  Get(table, key) : super([table, key]);

  @override
  call(attr) {
    return GetField(this, attr);
  }
}

class GetAll extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.GET_ALL;

  GetAll(keys, [options]) : super(keys, options);

  @override
  call(attr) {
    return GetField(this, attr);
  }
}

class Reduce extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.REDUCE;

  Reduce(seq, reductionFunction, [base])
      : super([seq, reductionFunction], base);
}

class Sum extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.SUM;

  Sum(obj, args) : super([obj, args]);
}

class Avg extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.AVG;

  Avg(obj, args) : super([obj, args]);
}

class Min extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.MIN;

  Min(obj, args) : super([obj, args]);
}

class Max extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.MAX;

  Max(obj, args) : super([obj, args]);
}

class RqlMap extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.MAP;

  RqlMap(argslist, expression) : super() {
    int? argsCount = argslist.length;
    var temp = [];
    temp.addAll(argslist);
    temp.add(_funcWrap(expression, argsCount));
    args.addAll(temp.map((arg) {
      return _expr(arg, defaultNestingDepth, argsCount);
    }));
  }
}

class Filter extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.FILTER;

  Filter(selection, predicate, [Map? options])
      : super([selection, predicate], options);
}

class ConcatMap extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.CONCAT_MAP;

  ConcatMap(seq, mappingFunction) : super([seq, mappingFunction]);
}

class OrderBy extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.ORDER_BY;

  OrderBy(args, [Map? options]) : super(args, options);
}

class Distinct extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.DISTINCT;

  Distinct(sequence) : super([sequence]);
}

class Count extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.COUNT;

  Count([seq, filter]) : super([seq, filter]);
}

class Union extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.UNION;

  Union(first, second) : super([first, second]);
}

class Nth extends RqlBracketQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.NTH;

  Nth(selection, int index) : super([selection, index]);
}

class Match extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.MATCH;

  Match(obj, regex) : super([obj, regex]);
}

class Split extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.SPLIT;

  Split(tbl, [obj, maxSplits]) : super([tbl, obj, maxSplits]);
}

class Upcase extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.UPCASE;

  Upcase(obj) : super([obj]);
}

class Downcase extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.DOWNCASE;

  Downcase(obj) : super([obj]);
}

class OffsetsOf extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.OFFSETS_OF;

  OffsetsOf(seq, index) : super([seq, index]);
}

class IsEmpty extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.IS_EMPTY;

  IsEmpty(selection) : super([selection]);
}

class Group extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.GROUP;

  Group(obj, groups, [options]) : super([obj, ...groups], options);
}

class InnerJoin extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.INNER_JOIN;

  InnerJoin(first, second, predicate) : super([first, second, predicate]);
}

class OuterJoin extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.OUTER_JOIN;

  OuterJoin(first, second, predicate) : super([first, second, predicate]);
}

class EqJoin extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.EQ_JOIN;

  EqJoin(first, second, predicate, [Map? options])
      : super([first, second, predicate], options);
}

class Zip extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.ZIP;

  Zip(seq) : super([seq]);
}

class CoerceTo extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.COERCE_TO;

  CoerceTo(obj, String type) : super([obj, type]);
}

class Ungroup extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.UNGROUP;

  Ungroup(obj) : super([obj]);
}

class TypeOf extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.TYPE_OF;

  TypeOf(obj) : super([obj]);
}

class Update extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.UPDATE;

  Update(tbl, expression, [Map? options]) : super([tbl, expression], options);
}

class Delete extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.DELETE;

  Delete(selection, [Map? options]) : super([selection], options);
}

class Replace extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.REPLACE;

  Replace(table, expression, [options]) : super([table, expression], options);
}

class Insert extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.INSERT;

  Insert(table, records, [Map? options]) : super([table, records], options);
}

class DbCreate extends RqlTopLevelQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.DB_CREATE;

  DbCreate(String dbName, [Map? options]) : super([dbName], options);
}

class DbDrop extends RqlTopLevelQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.DB_DROP;

  DbDrop(String dbName, [Map? options]) : super([dbName], options);
}

class DbList extends RqlTopLevelQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.DB_LIST;

  DbList() : super();
}

class Range extends RqlTopLevelQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.RANGE;

  Range(end) : super([end]);

  Range.asStream() : super();

  Range.withStart(start, end) : super([start, end]);
}

class TableCreate extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.TABLE_CREATE;

  TableCreate(table, [Map? options]) : super([table], options);

  TableCreate.fromDB(db, table, [Map? options]) : super([db, table], options);
}

class TableDrop extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.TABLE_DROP;

  TableDrop(tbl, [Map? options]) : super([tbl], options);

  TableDrop.fromDB(db, tbl, [Map? options]) : super([db, tbl], options);
}

class TableList extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.TABLE_LIST;

  TableList([db]) : super(db == null ? [] : [db]);
}

class IndexCreate extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.INDEX_CREATE;

  IndexCreate(tbl, index, [Map? options]) : super([tbl, index], options);

  IndexCreate.withIndexFunction(tbl, index, [indexFunction, Map? options])
      : super([tbl, index, indexFunction], options);
}

class IndexDrop extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.INDEX_DROP;

  IndexDrop(table, index) : super([table, index]);
}

class IndexRename extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.INDEX_RENAME;

  IndexRename(table, oldName, newName, options)
      : super([table, oldName, newName], options);
}

class IndexList extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.INDEX_LIST;

  IndexList(table) : super([table]);
}

class IndexStatus extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.INDEX_STATUS;

  IndexStatus(tbl, indexList)
      : super([tbl, indexList is List ? Args(indexList) : indexList]);
  IndexStatus.all(tbl) : super([tbl]);
}

class IndexWait extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.INDEX_WAIT;

  IndexWait(tbl, indexList)
      : super([tbl, indexList is List ? Args(indexList) : indexList]);
  IndexWait.all(tbl) : super([tbl]);
}

class Sync extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.SYNC;

  Sync(table) : super([table]);
}

class Branch extends RqlTopLevelQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.BRANCH;

  Branch(predicate, trueBranch, falseBranch)
      : super([predicate, trueBranch, falseBranch]);
  Branch.fromArgs(Args args) : super([args]);
}

class Or extends RqlBoolOperQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.OR;

  Or(orables) : super(orables);
}

class And extends RqlBoolOperQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.AND;

  And(andables) : super(andables);
}

class ForEach extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.FOR_EACH;

  ForEach(obj, writeQuery) : super([obj, writeQuery]);
}

class Info extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.INFO;

  Info(knowable) : super([knowable]);
}

class InsertAt extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.INSERT_AT;

  InsertAt(ar, index, value) : super([ar, index, value]);
}

class SpliceAt extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.SPLICE_AT;

  SpliceAt(ar, index, value) : super([ar, index, value]);
}

class DeleteAt extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.DELETE_AT;

  DeleteAt(ar, index, value) : super([ar, index, value]);
}

class ChangeAt extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.CHANGE_AT;

  ChangeAt(ar, index, value) : super([ar, index, value]);
}

class Sample extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.SAMPLE;

  Sample(selection, int i) : super([selection, i]);
}

class Uuid extends RqlQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.UUID;
  Uuid(str) : super(str == null ? [] : [str]);
}

class Json extends RqlTopLevelQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.JSON;

  Json(String jsonString, [Map? options]) : super([jsonString], options);
}

class Args extends RqlTopLevelQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.ARGS;

  Args(List array) : super([array]);
}

class ToISO8601 extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.TO_ISO8601;

  ToISO8601(obj) : super([obj]);
}

class During extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.DURING;

  During(obj, start, end, [Map? options]) : super([obj, start, end], options);
}

class Date extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.DATE;

  Date(obj) : super([obj]);
}

class TimeOfDay extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.TIME_OF_DAY;

  TimeOfDay(obj) : super([obj]);
}

class Timezone extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.TIMEZONE;

  Timezone(zone) : super([zone]);
}

class Year extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.YEAR;

  Year(year) : super([year]);
}

class Month extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.MONTH;

  Month(month) : super([month]);
}

class Day extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.DAY;

  Day(day) : super([day]);
}

class DayOfWeek extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.DAY_OF_WEEK;

  DayOfWeek(dow) : super([dow]);
}

class DayOfYear extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.DAY_OF_YEAR;

  DayOfYear(doy) : super([doy]);
}

class Hours extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.HOURS;

  Hours(hours) : super([hours]);
}

class Minutes extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.MINUTES;

  Minutes(minutes) : super([minutes]);
}

class Seconds extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.SECONDS;

  Seconds(seconds) : super([seconds]);
}

class Binary extends RqlTopLevelQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.BINARY;
  Binary(data) : super([data]);
}

class Time extends RqlTopLevelQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.TIME;

  Time(Args args) : super([args]);

  Time.withHour(int year, int month, int day, String timezone, int hour)
      : super([year, month, day, hour, timezone]);

  Time.withMinute(
      int year, int month, int day, String timezone, int hour, int minute)
      : super([year, month, day, hour, minute, timezone]);

  Time.withSecond(int year, int month, int day, String timezone, int hour,
      int minute, int second)
      : super([year, month, day, hour, minute, second, timezone]);
}

class RqlISO8601 extends RqlTopLevelQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.ISO8601;

  RqlISO8601(strTime, [defaultTimeZone = 'Z'])
      : super([strTime], {'default_timezone': defaultTimeZone});
}

class EpochTime extends RqlTopLevelQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.EPOCH_TIME;

  EpochTime(eptime) : super([eptime]);
}

class Now extends RqlTopLevelQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.NOW;

  Now() : super();
}

class InTimezone extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.IN_TIMEZONE;

  InTimezone(zoneable, tz) : super([zoneable, tz]);
}

class ToEpochTime extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.TO_EPOCH_TIME;

  ToEpochTime(obj) : super([obj]);
}

class Func extends RqlQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.FUNC;
  Function fun;
  int argsCount;
  static int nextId = 0;
  Func(this.fun, this.argsCount) : super(null, null) {
    var vrs = [];
    var vrids = [];

    for (var i = 0; i < argsCount; i++) {
      vrs.add(Var(Func.nextId));
      vrids.add(Func.nextId);
      Func.nextId++;
    }

    args = [MakeArray(vrids), _expr(Function.apply(fun, vrs))];
  }
}

class Asc extends RqlTopLevelQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.ASC;

  Asc(obj) : super([obj]);
}

class Desc extends RqlTopLevelQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.DESC;

  Desc(attr) : super([attr]);
}

class Literal extends RqlTopLevelQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.LITERAL;

  Literal(attr) : super([attr]);
}

class Circle extends RqlTopLevelQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.CIRCLE;

  Circle(point, radius, [Map? options]) : super([point, radius], options);
}

class Distance extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.DISTANCE;

  Distance(obj, geo, [Map? options]) : super([obj, geo], options);
}

class Fill extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.FILL;

  Fill(obj) : super([obj]);
}

class GeoJson extends RqlTopLevelQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.GEOJSON;

  GeoJson(Map geoJson) : super([geoJson]);
}

class ToGeoJson extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.TO_GEOJSON;

  ToGeoJson(obj) : super([obj]);
}

class GetIntersecting extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.GET_INTERSECTING;

  GetIntersecting(table, geo, [Map? options]) : super([table, geo], options);
}

class GetNearest extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.GET_NEAREST;

  GetNearest(table, point, Map? options) : super([table, point], options);
}

class Includes extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.INCLUDES;

  Includes(obj, geo) : super([obj, geo]);
}

class Intersects extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.INTERSECTS;

  Intersects(obj, geo) : super([obj, geo]);
}

class Line extends RqlTopLevelQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.LINE;

  Line(points) : super(points);
}

class Point extends RqlTopLevelQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.POINT;

  Point(long, lat) : super([long, lat]);
}

class Polygon extends RqlTopLevelQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.POLYGON;

  Polygon(points) : super(points);
}

class PolygonSub extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.POLYGON_SUB;

  PolygonSub(var poly1, var poly2) : super([poly1, poly2]);
}

class Config extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.CONFIG;

  Config(obj) : super([obj]);
}

class Rebalance extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.REBALANCE;

  Rebalance(obj) : super([obj]);
}

class Reconfigure extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.RECONFIGURE;

  Reconfigure(obj, Map options) : super([obj], options);
}

class Status extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.STATUS;

  Status(obj) : super([obj]);
}

class Wait extends RqlMethodQuery {
  @override
  p.Term_TermType? tt = p.Term_TermType.WAIT;

  Wait(obj, [Map? options]) : super([obj], options);
}

class RqlTimeName extends RqlQuery {
  @override
  p.Term_TermType? tt;

  RqlTimeName(this.tt) : super();
}

class RqlConstant extends RqlQuery {
  @override
  p.Term_TermType? tt;

  RqlConstant(this.tt) : super();
}

class _RqlAllOptions {
  //list of every option from any term
  late List options;

  _RqlAllOptions(p.Term_TermType? tt) {
    switch (tt) {
      case p.Term_TermType.TABLE_CREATE:
        options = ['primary_key', 'durability', 'datacenter'];
        break;
      case p.Term_TermType.INSERT:
        options = ['durability', 'return_changes', 'conflict'];
        break;
      case p.Term_TermType.UPDATE:
        options = ['durability', 'return_changes', 'non_atomic'];
        break;
      case p.Term_TermType.REPLACE:
        options = ['durability', 'return_changes', 'non_atomic'];
        break;
      case p.Term_TermType.DELETE:
        options = ['durability', 'return_changes'];
        break;
      case p.Term_TermType.TABLE:
        options = ['read_mode'];
        break;
      case p.Term_TermType.INDEX_CREATE:
        options = ['multi'];
        break;
      case p.Term_TermType.GET_ALL:
        options = ['index'];
        break;
      case p.Term_TermType.BETWEEN:
        options = ['index', 'left_bound', 'right_bound'];
        break;
      case p.Term_TermType.FILTER:
        options = ['default'];
        break;
      case p.Term_TermType.CHANGES:
        options = ['includeOffsets', 'includeTypes'];
        break;
      case p.Term_TermType.EQ_JOIN:
        options = ['index', 'ordered'];
        break;
      case p.Term_TermType.UNION:
        options = ['interleave'];
        break;
      case p.Term_TermType.SLICE:
        options = ['left_bound', 'right_bound'];
        break;
      case p.Term_TermType.GROUP:
        options = ['index'];
        break;
      case p.Term_TermType.RANDOM:
        options = ['float'];
        break;
      case p.Term_TermType.ISO8601:
        options = ['default_timezone'];
        break;
      case p.Term_TermType.DURING:
        options = ['left_bound', 'right_bound'];
        break;
      case p.Term_TermType.JAVASCRIPT:
        options = ['timeout'];
        break;
      case p.Term_TermType.HTTP:
        options = [
          'timeout',
          'attempts',
          'redirects',
          'verify',
          'result_format',
          'method',
          'auth',
          'params',
          'header',
          'data',
          'page',
          'page_limit'
        ];
        break;
      case p.Term_TermType.CIRCLE:
        options = ['num_vertices', 'geo_system', 'unit', 'fill'];
        break;
      case p.Term_TermType.GET_NEAREST:
        options = ['index', 'max_results', 'max_dist', 'unit', 'geo_system'];
        break;
      case p.Term_TermType.RECONFIGURE:
        options = [
          'shards',
          'replicas',
          'primary_replica_tag',
          'dry_run',
          'emergency_repair'
        ];
        break;
      case p.Term_TermType.WAIT:
        options = ['wait_for', 'timeout'];
        break;
      default:
        options = [];
    }
  }
}
