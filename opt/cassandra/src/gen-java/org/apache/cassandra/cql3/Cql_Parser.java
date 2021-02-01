// $ANTLR 3.5.2 Parser.g 2019-11-28 17:22:05

    package org.apache.cassandra.cql3;

    import java.util.Collections;
    import java.util.EnumSet;
    import java.util.HashSet;
    import java.util.LinkedHashMap;
    import java.util.List;
    import java.util.Map;
    import java.util.Set;

    import org.apache.cassandra.auth.*;
    import org.apache.cassandra.cql3.conditions.*;
    import org.apache.cassandra.cql3.functions.*;
    import org.apache.cassandra.cql3.restrictions.CustomIndexExpression;
    import org.apache.cassandra.cql3.selection.*;
    import org.apache.cassandra.cql3.statements.*;
    import org.apache.cassandra.cql3.statements.schema.*;
    import org.apache.cassandra.exceptions.ConfigurationException;
    import org.apache.cassandra.exceptions.InvalidRequestException;
    import org.apache.cassandra.exceptions.SyntaxException;
    import org.apache.cassandra.schema.ColumnMetadata;
    import org.apache.cassandra.utils.Pair;


import org.antlr.runtime.*;
import java.util.Stack;
import java.util.List;
import java.util.ArrayList;
import java.util.Map;
import java.util.HashMap;

@SuppressWarnings("all")
public class Cql_Parser extends Parser {
	public static final int EOF=-1;
	public static final int T__188=188;
	public static final int T__189=189;
	public static final int T__190=190;
	public static final int T__191=191;
	public static final int T__192=192;
	public static final int T__193=193;
	public static final int T__194=194;
	public static final int T__195=195;
	public static final int T__196=196;
	public static final int T__197=197;
	public static final int T__198=198;
	public static final int T__199=199;
	public static final int T__200=200;
	public static final int T__201=201;
	public static final int T__202=202;
	public static final int T__203=203;
	public static final int T__204=204;
	public static final int T__205=205;
	public static final int T__206=206;
	public static final int T__207=207;
	public static final int T__208=208;
	public static final int T__209=209;
	public static final int T__210=210;
	public static final int T__211=211;
	public static final int A=4;
	public static final int B=5;
	public static final int BOOLEAN=6;
	public static final int C=7;
	public static final int COMMENT=8;
	public static final int D=9;
	public static final int DIGIT=10;
	public static final int DURATION=11;
	public static final int DURATION_UNIT=12;
	public static final int E=13;
	public static final int EMPTY_QUOTED_NAME=14;
	public static final int EXPONENT=15;
	public static final int F=16;
	public static final int FLOAT=17;
	public static final int G=18;
	public static final int H=19;
	public static final int HEX=20;
	public static final int HEXNUMBER=21;
	public static final int I=22;
	public static final int IDENT=23;
	public static final int INTEGER=24;
	public static final int J=25;
	public static final int K=26;
	public static final int K_ACCESS=27;
	public static final int K_ADD=28;
	public static final int K_AGGREGATE=29;
	public static final int K_ALL=30;
	public static final int K_ALLOW=31;
	public static final int K_ALTER=32;
	public static final int K_AND=33;
	public static final int K_APPLY=34;
	public static final int K_AS=35;
	public static final int K_ASC=36;
	public static final int K_ASCII=37;
	public static final int K_AUTHORIZE=38;
	public static final int K_BATCH=39;
	public static final int K_BEGIN=40;
	public static final int K_BIGINT=41;
	public static final int K_BLOB=42;
	public static final int K_BOOLEAN=43;
	public static final int K_BY=44;
	public static final int K_CALLED=45;
	public static final int K_CAST=46;
	public static final int K_CLUSTERING=47;
	public static final int K_COLUMNFAMILY=48;
	public static final int K_COMPACT=49;
	public static final int K_CONTAINS=50;
	public static final int K_COUNT=51;
	public static final int K_COUNTER=52;
	public static final int K_CREATE=53;
	public static final int K_CUSTOM=54;
	public static final int K_DATACENTERS=55;
	public static final int K_DATE=56;
	public static final int K_DECIMAL=57;
	public static final int K_DEFAULT=58;
	public static final int K_DELETE=59;
	public static final int K_DESC=60;
	public static final int K_DESCRIBE=61;
	public static final int K_DISTINCT=62;
	public static final int K_DOUBLE=63;
	public static final int K_DROP=64;
	public static final int K_DURATION=65;
	public static final int K_ENTRIES=66;
	public static final int K_EXECUTE=67;
	public static final int K_EXISTS=68;
	public static final int K_FILTERING=69;
	public static final int K_FINALFUNC=70;
	public static final int K_FLOAT=71;
	public static final int K_FROM=72;
	public static final int K_FROZEN=73;
	public static final int K_FULL=74;
	public static final int K_FUNCTION=75;
	public static final int K_FUNCTIONS=76;
	public static final int K_GRANT=77;
	public static final int K_GROUP=78;
	public static final int K_IF=79;
	public static final int K_IN=80;
	public static final int K_INDEX=81;
	public static final int K_INET=82;
	public static final int K_INITCOND=83;
	public static final int K_INPUT=84;
	public static final int K_INSERT=85;
	public static final int K_INT=86;
	public static final int K_INTO=87;
	public static final int K_IS=88;
	public static final int K_JSON=89;
	public static final int K_KEY=90;
	public static final int K_KEYS=91;
	public static final int K_KEYSPACE=92;
	public static final int K_KEYSPACES=93;
	public static final int K_LANGUAGE=94;
	public static final int K_LIKE=95;
	public static final int K_LIMIT=96;
	public static final int K_LIST=97;
	public static final int K_LOGIN=98;
	public static final int K_MAP=99;
	public static final int K_MATERIALIZED=100;
	public static final int K_MBEAN=101;
	public static final int K_MBEANS=102;
	public static final int K_MODIFY=103;
	public static final int K_NEGATIVE_INFINITY=104;
	public static final int K_NEGATIVE_NAN=105;
	public static final int K_NOLOGIN=106;
	public static final int K_NORECURSIVE=107;
	public static final int K_NOSUPERUSER=108;
	public static final int K_NOT=109;
	public static final int K_NULL=110;
	public static final int K_OF=111;
	public static final int K_ON=112;
	public static final int K_OPTIONS=113;
	public static final int K_OR=114;
	public static final int K_ORDER=115;
	public static final int K_PARTITION=116;
	public static final int K_PASSWORD=117;
	public static final int K_PER=118;
	public static final int K_PERMISSION=119;
	public static final int K_PERMISSIONS=120;
	public static final int K_POSITIVE_INFINITY=121;
	public static final int K_POSITIVE_NAN=122;
	public static final int K_PRIMARY=123;
	public static final int K_RENAME=124;
	public static final int K_REPLACE=125;
	public static final int K_RETURNS=126;
	public static final int K_REVOKE=127;
	public static final int K_ROLE=128;
	public static final int K_ROLES=129;
	public static final int K_SELECT=130;
	public static final int K_SET=131;
	public static final int K_SFUNC=132;
	public static final int K_SMALLINT=133;
	public static final int K_STATIC=134;
	public static final int K_STORAGE=135;
	public static final int K_STYPE=136;
	public static final int K_SUPERUSER=137;
	public static final int K_TEXT=138;
	public static final int K_TIME=139;
	public static final int K_TIMESTAMP=140;
	public static final int K_TIMEUUID=141;
	public static final int K_TINYINT=142;
	public static final int K_TO=143;
	public static final int K_TOKEN=144;
	public static final int K_TRIGGER=145;
	public static final int K_TRUNCATE=146;
	public static final int K_TTL=147;
	public static final int K_TUPLE=148;
	public static final int K_TYPE=149;
	public static final int K_UNLOGGED=150;
	public static final int K_UNSET=151;
	public static final int K_UPDATE=152;
	public static final int K_USE=153;
	public static final int K_USER=154;
	public static final int K_USERS=155;
	public static final int K_USING=156;
	public static final int K_UUID=157;
	public static final int K_VALUES=158;
	public static final int K_VARCHAR=159;
	public static final int K_VARINT=160;
	public static final int K_VIEW=161;
	public static final int K_WHERE=162;
	public static final int K_WITH=163;
	public static final int K_WRITETIME=164;
	public static final int L=165;
	public static final int LETTER=166;
	public static final int M=167;
	public static final int MULTILINE_COMMENT=168;
	public static final int N=169;
	public static final int O=170;
	public static final int P=171;
	public static final int Q=172;
	public static final int QMARK=173;
	public static final int QUOTED_NAME=174;
	public static final int R=175;
	public static final int RANGE=176;
	public static final int S=177;
	public static final int STRING_LITERAL=178;
	public static final int T=179;
	public static final int U=180;
	public static final int UUID=181;
	public static final int V=182;
	public static final int W=183;
	public static final int WS=184;
	public static final int X=185;
	public static final int Y=186;
	public static final int Z=187;

	// delegates
	public Parser[] getDelegates() {
		return new Parser[] {};
	}

	// delegators
	public CqlParser gCql;
	public CqlParser gParent;


	public Cql_Parser(TokenStream input, CqlParser gCql) {
		this(input, new RecognizerSharedState(), gCql);
	}
	public Cql_Parser(TokenStream input, RecognizerSharedState state, CqlParser gCql) {
		super(input, state);
		this.gCql = gCql;
		gParent = gCql;
	}

	@Override public String[] getTokenNames() { return CqlParser.tokenNames; }
	@Override public String getGrammarFileName() { return "Parser.g"; }


	    private final List<ErrorListener> listeners = new ArrayList<ErrorListener>();
	    protected final List<ColumnIdentifier> bindVariables = new ArrayList<ColumnIdentifier>();

	    public static final Set<String> reservedTypeNames = new HashSet<String>()
	    {{
	        add("byte");
	        add("complex");
	        add("enum");
	        add("date");
	        add("interval");
	        add("macaddr");
	        add("bitstring");
	    }};

	    public AbstractMarker.Raw newBindVariables(ColumnIdentifier name)
	    {
	        AbstractMarker.Raw marker = new AbstractMarker.Raw(bindVariables.size());
	        bindVariables.add(name);
	        return marker;
	    }

	    public AbstractMarker.INRaw newINBindVariables(ColumnIdentifier name)
	    {
	        AbstractMarker.INRaw marker = new AbstractMarker.INRaw(bindVariables.size());
	        bindVariables.add(name);
	        return marker;
	    }

	    public Tuples.Raw newTupleBindVariables(ColumnIdentifier name)
	    {
	        Tuples.Raw marker = new Tuples.Raw(bindVariables.size());
	        bindVariables.add(name);
	        return marker;
	    }

	    public Tuples.INRaw newTupleINBindVariables(ColumnIdentifier name)
	    {
	        Tuples.INRaw marker = new Tuples.INRaw(bindVariables.size());
	        bindVariables.add(name);
	        return marker;
	    }

	    public Json.Marker newJsonBindVariables(ColumnIdentifier name)
	    {
	        Json.Marker marker = new Json.Marker(bindVariables.size());
	        bindVariables.add(name);
	        return marker;
	    }

	    public void addErrorListener(ErrorListener listener)
	    {
	        this.listeners.add(listener);
	    }

	    public void removeErrorListener(ErrorListener listener)
	    {
	        this.listeners.remove(listener);
	    }

	    public void displayRecognitionError(String[] tokenNames, RecognitionException e)
	    {
	        for (int i = 0, m = listeners.size(); i < m; i++)
	            listeners.get(i).syntaxError(this, tokenNames, e);
	    }

	    protected void addRecognitionError(String msg)
	    {
	        for (int i = 0, m = listeners.size(); i < m; i++)
	            listeners.get(i).syntaxError(this, msg);
	    }

	    public Map<String, String> convertPropertyMap(Maps.Literal map)
	    {
	        if (map == null || map.entries == null || map.entries.isEmpty())
	            return Collections.<String, String>emptyMap();

	        Map<String, String> res = new HashMap<>(map.entries.size());

	        for (Pair<Term.Raw, Term.Raw> entry : map.entries)
	        {
	            // Because the parser tries to be smart and recover on error (to
	            // allow displaying more than one error I suppose), we have null
	            // entries in there. Just skip those, a proper error will be thrown in the end.
	            if (entry.left == null || entry.right == null)
	                break;

	            if (!(entry.left instanceof Constants.Literal))
	            {
	                String msg = "Invalid property name: " + entry.left;
	                if (entry.left instanceof AbstractMarker.Raw)
	                    msg += " (bind variables are not supported in DDL queries)";
	                addRecognitionError(msg);
	                break;
	            }
	            if (!(entry.right instanceof Constants.Literal))
	            {
	                String msg = "Invalid property value: " + entry.right + " for property: " + entry.left;
	                if (entry.right instanceof AbstractMarker.Raw)
	                    msg += " (bind variables are not supported in DDL queries)";
	                addRecognitionError(msg);
	                break;
	            }

	            if (res.put(((Constants.Literal)entry.left).getRawText(), ((Constants.Literal)entry.right).getRawText()) != null)
	            {
	                addRecognitionError(String.format("Multiple definition for property " + ((Constants.Literal)entry.left).getRawText()));
	            }
	        }

	        return res;
	    }

	    public void addRawUpdate(List<Pair<ColumnMetadata.Raw, Operation.RawUpdate>> operations, ColumnMetadata.Raw key, Operation.RawUpdate update)
	    {
	        for (Pair<ColumnMetadata.Raw, Operation.RawUpdate> p : operations)
	        {
	            if (p.left.equals(key) && !p.right.isCompatibleWith(update))
	                addRecognitionError("Multiple incompatible setting of column " + key);
	        }
	        operations.add(Pair.create(key, update));
	    }

	    public Set<Permission> filterPermissions(Set<Permission> permissions, IResource resource)
	    {
	        if (resource == null)
	            return Collections.emptySet();
	        Set<Permission> filtered = new HashSet<>(permissions);
	        filtered.retainAll(resource.applicablePermissions());
	        if (filtered.isEmpty())
	            addRecognitionError("Resource type " + resource.getClass().getSimpleName() +
	                                    " does not support any of the requested permissions");

	        return filtered;
	    }

	    public String canonicalizeObjectName(String s, boolean enforcePattern)
	    {
	        // these two conditions are here because technically they are valid
	        // ObjectNames, but we want to restrict their use without adding unnecessary
	        // work to JMXResource construction as that also happens on hotter code paths
	        if ("".equals(s))
	            addRecognitionError("Empty JMX object name supplied");

	        if ("*:*".equals(s))
	            addRecognitionError("Please use ALL MBEANS instead of wildcard pattern");

	        try
	        {
	            javax.management.ObjectName objectName = javax.management.ObjectName.getInstance(s);
	            if (enforcePattern && !objectName.isPattern())
	                addRecognitionError("Plural form used, but non-pattern JMX object name specified (" + s + ")");
	            return objectName.getCanonicalName();
	        }
	        catch (javax.management.MalformedObjectNameException e)
	        {
	          addRecognitionError(s + " is not a valid JMX object name");
	          return s;
	        }
	    }

	    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////
	    // Recovery methods are overridden to avoid wasting work on recovering from errors when the result will be
	    // ignored anyway.
	    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////

	    @Override
	    protected Object recoverFromMismatchedToken(IntStream input, int ttype, BitSet follow) throws RecognitionException
	    {
	        throw new MismatchedTokenException(ttype, input);
	    }

	    @Override
	    public void recover(IntStream input, RecognitionException re)
	    {
	        // Do nothing.
	    }



	// $ANTLR start "cqlStatement"
	// Parser.g:207:1: cqlStatement returns [CQLStatement.Raw stmt] : (st1= selectStatement |st2= insertStatement |st3= updateStatement |st4= batchStatement |st5= deleteStatement |st6= useStatement |st7= truncateStatement |st8= createKeyspaceStatement |st9= createTableStatement |st10= createIndexStatement |st11= dropKeyspaceStatement |st12= dropTableStatement |st13= dropIndexStatement |st14= alterTableStatement |st15= alterKeyspaceStatement |st16= grantPermissionsStatement |st17= revokePermissionsStatement |st18= listPermissionsStatement |st19= createUserStatement |st20= alterUserStatement |st21= dropUserStatement |st22= listUsersStatement |st23= createTriggerStatement |st24= dropTriggerStatement |st25= createTypeStatement |st26= alterTypeStatement |st27= dropTypeStatement |st28= createFunctionStatement |st29= dropFunctionStatement |st30= createAggregateStatement |st31= dropAggregateStatement |st32= createRoleStatement |st33= alterRoleStatement |st34= dropRoleStatement |st35= listRolesStatement |st36= grantRoleStatement |st37= revokeRoleStatement |st38= createMaterializedViewStatement |st39= dropMaterializedViewStatement |st40= alterMaterializedViewStatement );
	public final CQLStatement.Raw cqlStatement() throws RecognitionException {
		CQLStatement.Raw stmt = null;


		SelectStatement.RawStatement st1 =null;
		ModificationStatement.Parsed st2 =null;
		UpdateStatement.ParsedUpdate st3 =null;
		BatchStatement.Parsed st4 =null;
		DeleteStatement.Parsed st5 =null;
		UseStatement st6 =null;
		TruncateStatement st7 =null;
		CreateKeyspaceStatement.Raw st8 =null;
		CreateTableStatement.Raw st9 =null;
		CreateIndexStatement.Raw st10 =null;
		DropKeyspaceStatement.Raw st11 =null;
		DropTableStatement.Raw st12 =null;
		DropIndexStatement.Raw st13 =null;
		AlterTableStatement.Raw st14 =null;
		AlterKeyspaceStatement.Raw st15 =null;
		GrantPermissionsStatement st16 =null;
		RevokePermissionsStatement st17 =null;
		ListPermissionsStatement st18 =null;
		CreateRoleStatement st19 =null;
		AlterRoleStatement st20 =null;
		DropRoleStatement st21 =null;
		ListRolesStatement st22 =null;
		CreateTriggerStatement.Raw st23 =null;
		DropTriggerStatement.Raw st24 =null;
		CreateTypeStatement.Raw st25 =null;
		AlterTypeStatement.Raw st26 =null;
		DropTypeStatement.Raw st27 =null;
		CreateFunctionStatement.Raw st28 =null;
		DropFunctionStatement.Raw st29 =null;
		CreateAggregateStatement.Raw st30 =null;
		DropAggregateStatement.Raw st31 =null;
		CreateRoleStatement st32 =null;
		AlterRoleStatement st33 =null;
		DropRoleStatement st34 =null;
		ListRolesStatement st35 =null;
		GrantRoleStatement st36 =null;
		RevokeRoleStatement st37 =null;
		CreateViewStatement.Raw st38 =null;
		DropViewStatement.Raw st39 =null;
		AlterViewStatement.Raw st40 =null;

		try {
			// Parser.g:209:5: (st1= selectStatement |st2= insertStatement |st3= updateStatement |st4= batchStatement |st5= deleteStatement |st6= useStatement |st7= truncateStatement |st8= createKeyspaceStatement |st9= createTableStatement |st10= createIndexStatement |st11= dropKeyspaceStatement |st12= dropTableStatement |st13= dropIndexStatement |st14= alterTableStatement |st15= alterKeyspaceStatement |st16= grantPermissionsStatement |st17= revokePermissionsStatement |st18= listPermissionsStatement |st19= createUserStatement |st20= alterUserStatement |st21= dropUserStatement |st22= listUsersStatement |st23= createTriggerStatement |st24= dropTriggerStatement |st25= createTypeStatement |st26= alterTypeStatement |st27= dropTypeStatement |st28= createFunctionStatement |st29= dropFunctionStatement |st30= createAggregateStatement |st31= dropAggregateStatement |st32= createRoleStatement |st33= alterRoleStatement |st34= dropRoleStatement |st35= listRolesStatement |st36= grantRoleStatement |st37= revokeRoleStatement |st38= createMaterializedViewStatement |st39= dropMaterializedViewStatement |st40= alterMaterializedViewStatement )
			int alt1=40;
			alt1 = dfa1.predict(input);
			switch (alt1) {
				case 1 :
					// Parser.g:209:7: st1= selectStatement
					{
					pushFollow(FOLLOW_selectStatement_in_cqlStatement59);
					st1=selectStatement();
					state._fsp--;
					if (state.failed) return stmt;
					if ( state.backtracking==0 ) { stmt = st1; }
					}
					break;
				case 2 :
					// Parser.g:210:7: st2= insertStatement
					{
					pushFollow(FOLLOW_insertStatement_in_cqlStatement88);
					st2=insertStatement();
					state._fsp--;
					if (state.failed) return stmt;
					if ( state.backtracking==0 ) { stmt = st2; }
					}
					break;
				case 3 :
					// Parser.g:211:7: st3= updateStatement
					{
					pushFollow(FOLLOW_updateStatement_in_cqlStatement117);
					st3=updateStatement();
					state._fsp--;
					if (state.failed) return stmt;
					if ( state.backtracking==0 ) { stmt = st3; }
					}
					break;
				case 4 :
					// Parser.g:212:7: st4= batchStatement
					{
					pushFollow(FOLLOW_batchStatement_in_cqlStatement146);
					st4=batchStatement();
					state._fsp--;
					if (state.failed) return stmt;
					if ( state.backtracking==0 ) { stmt = st4; }
					}
					break;
				case 5 :
					// Parser.g:213:7: st5= deleteStatement
					{
					pushFollow(FOLLOW_deleteStatement_in_cqlStatement176);
					st5=deleteStatement();
					state._fsp--;
					if (state.failed) return stmt;
					if ( state.backtracking==0 ) { stmt = st5; }
					}
					break;
				case 6 :
					// Parser.g:214:7: st6= useStatement
					{
					pushFollow(FOLLOW_useStatement_in_cqlStatement205);
					st6=useStatement();
					state._fsp--;
					if (state.failed) return stmt;
					if ( state.backtracking==0 ) { stmt = st6; }
					}
					break;
				case 7 :
					// Parser.g:215:7: st7= truncateStatement
					{
					pushFollow(FOLLOW_truncateStatement_in_cqlStatement237);
					st7=truncateStatement();
					state._fsp--;
					if (state.failed) return stmt;
					if ( state.backtracking==0 ) { stmt = st7; }
					}
					break;
				case 8 :
					// Parser.g:216:7: st8= createKeyspaceStatement
					{
					pushFollow(FOLLOW_createKeyspaceStatement_in_cqlStatement264);
					st8=createKeyspaceStatement();
					state._fsp--;
					if (state.failed) return stmt;
					if ( state.backtracking==0 ) { stmt = st8; }
					}
					break;
				case 9 :
					// Parser.g:217:7: st9= createTableStatement
					{
					pushFollow(FOLLOW_createTableStatement_in_cqlStatement285);
					st9=createTableStatement();
					state._fsp--;
					if (state.failed) return stmt;
					if ( state.backtracking==0 ) { stmt = st9; }
					}
					break;
				case 10 :
					// Parser.g:218:7: st10= createIndexStatement
					{
					pushFollow(FOLLOW_createIndexStatement_in_cqlStatement308);
					st10=createIndexStatement();
					state._fsp--;
					if (state.failed) return stmt;
					if ( state.backtracking==0 ) { stmt = st10; }
					}
					break;
				case 11 :
					// Parser.g:219:7: st11= dropKeyspaceStatement
					{
					pushFollow(FOLLOW_dropKeyspaceStatement_in_cqlStatement331);
					st11=dropKeyspaceStatement();
					state._fsp--;
					if (state.failed) return stmt;
					if ( state.backtracking==0 ) { stmt = st11; }
					}
					break;
				case 12 :
					// Parser.g:220:7: st12= dropTableStatement
					{
					pushFollow(FOLLOW_dropTableStatement_in_cqlStatement353);
					st12=dropTableStatement();
					state._fsp--;
					if (state.failed) return stmt;
					if ( state.backtracking==0 ) { stmt = st12; }
					}
					break;
				case 13 :
					// Parser.g:221:7: st13= dropIndexStatement
					{
					pushFollow(FOLLOW_dropIndexStatement_in_cqlStatement378);
					st13=dropIndexStatement();
					state._fsp--;
					if (state.failed) return stmt;
					if ( state.backtracking==0 ) { stmt = st13; }
					}
					break;
				case 14 :
					// Parser.g:222:7: st14= alterTableStatement
					{
					pushFollow(FOLLOW_alterTableStatement_in_cqlStatement403);
					st14=alterTableStatement();
					state._fsp--;
					if (state.failed) return stmt;
					if ( state.backtracking==0 ) { stmt = st14; }
					}
					break;
				case 15 :
					// Parser.g:223:7: st15= alterKeyspaceStatement
					{
					pushFollow(FOLLOW_alterKeyspaceStatement_in_cqlStatement427);
					st15=alterKeyspaceStatement();
					state._fsp--;
					if (state.failed) return stmt;
					if ( state.backtracking==0 ) { stmt = st15; }
					}
					break;
				case 16 :
					// Parser.g:224:7: st16= grantPermissionsStatement
					{
					pushFollow(FOLLOW_grantPermissionsStatement_in_cqlStatement448);
					st16=grantPermissionsStatement();
					state._fsp--;
					if (state.failed) return stmt;
					if ( state.backtracking==0 ) { stmt = st16; }
					}
					break;
				case 17 :
					// Parser.g:225:7: st17= revokePermissionsStatement
					{
					pushFollow(FOLLOW_revokePermissionsStatement_in_cqlStatement466);
					st17=revokePermissionsStatement();
					state._fsp--;
					if (state.failed) return stmt;
					if ( state.backtracking==0 ) { stmt = st17; }
					}
					break;
				case 18 :
					// Parser.g:226:7: st18= listPermissionsStatement
					{
					pushFollow(FOLLOW_listPermissionsStatement_in_cqlStatement483);
					st18=listPermissionsStatement();
					state._fsp--;
					if (state.failed) return stmt;
					if ( state.backtracking==0 ) { stmt = st18; }
					}
					break;
				case 19 :
					// Parser.g:227:7: st19= createUserStatement
					{
					pushFollow(FOLLOW_createUserStatement_in_cqlStatement502);
					st19=createUserStatement();
					state._fsp--;
					if (state.failed) return stmt;
					if ( state.backtracking==0 ) { stmt = st19; }
					}
					break;
				case 20 :
					// Parser.g:228:7: st20= alterUserStatement
					{
					pushFollow(FOLLOW_alterUserStatement_in_cqlStatement526);
					st20=alterUserStatement();
					state._fsp--;
					if (state.failed) return stmt;
					if ( state.backtracking==0 ) { stmt = st20; }
					}
					break;
				case 21 :
					// Parser.g:229:7: st21= dropUserStatement
					{
					pushFollow(FOLLOW_dropUserStatement_in_cqlStatement551);
					st21=dropUserStatement();
					state._fsp--;
					if (state.failed) return stmt;
					if ( state.backtracking==0 ) { stmt = st21; }
					}
					break;
				case 22 :
					// Parser.g:230:7: st22= listUsersStatement
					{
					pushFollow(FOLLOW_listUsersStatement_in_cqlStatement577);
					st22=listUsersStatement();
					state._fsp--;
					if (state.failed) return stmt;
					if ( state.backtracking==0 ) { stmt = st22; }
					}
					break;
				case 23 :
					// Parser.g:231:7: st23= createTriggerStatement
					{
					pushFollow(FOLLOW_createTriggerStatement_in_cqlStatement602);
					st23=createTriggerStatement();
					state._fsp--;
					if (state.failed) return stmt;
					if ( state.backtracking==0 ) { stmt = st23; }
					}
					break;
				case 24 :
					// Parser.g:232:7: st24= dropTriggerStatement
					{
					pushFollow(FOLLOW_dropTriggerStatement_in_cqlStatement623);
					st24=dropTriggerStatement();
					state._fsp--;
					if (state.failed) return stmt;
					if ( state.backtracking==0 ) { stmt = st24; }
					}
					break;
				case 25 :
					// Parser.g:233:7: st25= createTypeStatement
					{
					pushFollow(FOLLOW_createTypeStatement_in_cqlStatement646);
					st25=createTypeStatement();
					state._fsp--;
					if (state.failed) return stmt;
					if ( state.backtracking==0 ) { stmt = st25; }
					}
					break;
				case 26 :
					// Parser.g:234:7: st26= alterTypeStatement
					{
					pushFollow(FOLLOW_alterTypeStatement_in_cqlStatement670);
					st26=alterTypeStatement();
					state._fsp--;
					if (state.failed) return stmt;
					if ( state.backtracking==0 ) { stmt = st26; }
					}
					break;
				case 27 :
					// Parser.g:235:7: st27= dropTypeStatement
					{
					pushFollow(FOLLOW_dropTypeStatement_in_cqlStatement695);
					st27=dropTypeStatement();
					state._fsp--;
					if (state.failed) return stmt;
					if ( state.backtracking==0 ) { stmt = st27; }
					}
					break;
				case 28 :
					// Parser.g:236:7: st28= createFunctionStatement
					{
					pushFollow(FOLLOW_createFunctionStatement_in_cqlStatement721);
					st28=createFunctionStatement();
					state._fsp--;
					if (state.failed) return stmt;
					if ( state.backtracking==0 ) { stmt = st28; }
					}
					break;
				case 29 :
					// Parser.g:237:7: st29= dropFunctionStatement
					{
					pushFollow(FOLLOW_dropFunctionStatement_in_cqlStatement741);
					st29=dropFunctionStatement();
					state._fsp--;
					if (state.failed) return stmt;
					if ( state.backtracking==0 ) { stmt = st29; }
					}
					break;
				case 30 :
					// Parser.g:238:7: st30= createAggregateStatement
					{
					pushFollow(FOLLOW_createAggregateStatement_in_cqlStatement763);
					st30=createAggregateStatement();
					state._fsp--;
					if (state.failed) return stmt;
					if ( state.backtracking==0 ) { stmt = st30; }
					}
					break;
				case 31 :
					// Parser.g:239:7: st31= dropAggregateStatement
					{
					pushFollow(FOLLOW_dropAggregateStatement_in_cqlStatement782);
					st31=dropAggregateStatement();
					state._fsp--;
					if (state.failed) return stmt;
					if ( state.backtracking==0 ) { stmt = st31; }
					}
					break;
				case 32 :
					// Parser.g:240:7: st32= createRoleStatement
					{
					pushFollow(FOLLOW_createRoleStatement_in_cqlStatement803);
					st32=createRoleStatement();
					state._fsp--;
					if (state.failed) return stmt;
					if ( state.backtracking==0 ) { stmt = st32; }
					}
					break;
				case 33 :
					// Parser.g:241:7: st33= alterRoleStatement
					{
					pushFollow(FOLLOW_alterRoleStatement_in_cqlStatement827);
					st33=alterRoleStatement();
					state._fsp--;
					if (state.failed) return stmt;
					if ( state.backtracking==0 ) { stmt = st33; }
					}
					break;
				case 34 :
					// Parser.g:242:7: st34= dropRoleStatement
					{
					pushFollow(FOLLOW_dropRoleStatement_in_cqlStatement852);
					st34=dropRoleStatement();
					state._fsp--;
					if (state.failed) return stmt;
					if ( state.backtracking==0 ) { stmt = st34; }
					}
					break;
				case 35 :
					// Parser.g:243:7: st35= listRolesStatement
					{
					pushFollow(FOLLOW_listRolesStatement_in_cqlStatement878);
					st35=listRolesStatement();
					state._fsp--;
					if (state.failed) return stmt;
					if ( state.backtracking==0 ) { stmt = st35; }
					}
					break;
				case 36 :
					// Parser.g:244:7: st36= grantRoleStatement
					{
					pushFollow(FOLLOW_grantRoleStatement_in_cqlStatement903);
					st36=grantRoleStatement();
					state._fsp--;
					if (state.failed) return stmt;
					if ( state.backtracking==0 ) { stmt = st36; }
					}
					break;
				case 37 :
					// Parser.g:245:7: st37= revokeRoleStatement
					{
					pushFollow(FOLLOW_revokeRoleStatement_in_cqlStatement928);
					st37=revokeRoleStatement();
					state._fsp--;
					if (state.failed) return stmt;
					if ( state.backtracking==0 ) { stmt = st37; }
					}
					break;
				case 38 :
					// Parser.g:246:7: st38= createMaterializedViewStatement
					{
					pushFollow(FOLLOW_createMaterializedViewStatement_in_cqlStatement952);
					st38=createMaterializedViewStatement();
					state._fsp--;
					if (state.failed) return stmt;
					if ( state.backtracking==0 ) { stmt = st38; }
					}
					break;
				case 39 :
					// Parser.g:247:7: st39= dropMaterializedViewStatement
					{
					pushFollow(FOLLOW_dropMaterializedViewStatement_in_cqlStatement964);
					st39=dropMaterializedViewStatement();
					state._fsp--;
					if (state.failed) return stmt;
					if ( state.backtracking==0 ) { stmt = st39; }
					}
					break;
				case 40 :
					// Parser.g:248:7: st40= alterMaterializedViewStatement
					{
					pushFollow(FOLLOW_alterMaterializedViewStatement_in_cqlStatement978);
					st40=alterMaterializedViewStatement();
					state._fsp--;
					if (state.failed) return stmt;
					if ( state.backtracking==0 ) { stmt = st40; }
					}
					break;

			}
			if ( state.backtracking==0 ) { if (stmt != null) stmt.setBindVariables(bindVariables); }
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return stmt;
	}
	// $ANTLR end "cqlStatement"



	// $ANTLR start "useStatement"
	// Parser.g:254:1: useStatement returns [UseStatement stmt] : K_USE ks= keyspaceName ;
	public final UseStatement useStatement() throws RecognitionException {
		UseStatement stmt = null;


		String ks =null;

		try {
			// Parser.g:255:5: ( K_USE ks= keyspaceName )
			// Parser.g:255:7: K_USE ks= keyspaceName
			{
			match(input,K_USE,FOLLOW_K_USE_in_useStatement1004); if (state.failed) return stmt;
			pushFollow(FOLLOW_keyspaceName_in_useStatement1008);
			ks=keyspaceName();
			state._fsp--;
			if (state.failed) return stmt;
			if ( state.backtracking==0 ) { stmt = new UseStatement(ks); }
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return stmt;
	}
	// $ANTLR end "useStatement"



	// $ANTLR start "selectStatement"
	// Parser.g:264:1: selectStatement returns [SelectStatement.RawStatement expr] : K_SELECT ( ( K_JSON selectClause )=> K_JSON )? sclause= selectClause K_FROM cf= columnFamilyName ( K_WHERE wclause= whereClause )? ( K_GROUP K_BY groupByClause[groups] ( ',' groupByClause[groups] )* )? ( K_ORDER K_BY orderByClause[orderings] ( ',' orderByClause[orderings] )* )? ( K_PER K_PARTITION K_LIMIT rows= intValue )? ( K_LIMIT rows= intValue )? ( K_ALLOW K_FILTERING )? ;
	public final SelectStatement.RawStatement selectStatement() throws RecognitionException {
		SelectStatement.RawStatement expr = null;


		ParserRuleReturnScope sclause =null;
		QualifiedName cf =null;
		WhereClause.Builder wclause =null;
		Term.Raw rows =null;


		        Term.Raw limit = null;
		        Term.Raw perPartitionLimit = null;
		        Map<ColumnMetadata.Raw, Boolean> orderings = new LinkedHashMap<>();
		        List<ColumnMetadata.Raw> groups = new ArrayList<>();
		        boolean allowFiltering = false;
		        boolean isJson = false;
		    
		try {
			// Parser.g:273:5: ( K_SELECT ( ( K_JSON selectClause )=> K_JSON )? sclause= selectClause K_FROM cf= columnFamilyName ( K_WHERE wclause= whereClause )? ( K_GROUP K_BY groupByClause[groups] ( ',' groupByClause[groups] )* )? ( K_ORDER K_BY orderByClause[orderings] ( ',' orderByClause[orderings] )* )? ( K_PER K_PARTITION K_LIMIT rows= intValue )? ( K_LIMIT rows= intValue )? ( K_ALLOW K_FILTERING )? )
			// Parser.g:273:7: K_SELECT ( ( K_JSON selectClause )=> K_JSON )? sclause= selectClause K_FROM cf= columnFamilyName ( K_WHERE wclause= whereClause )? ( K_GROUP K_BY groupByClause[groups] ( ',' groupByClause[groups] )* )? ( K_ORDER K_BY orderByClause[orderings] ( ',' orderByClause[orderings] )* )? ( K_PER K_PARTITION K_LIMIT rows= intValue )? ( K_LIMIT rows= intValue )? ( K_ALLOW K_FILTERING )?
			{
			match(input,K_SELECT,FOLLOW_K_SELECT_in_selectStatement1042); if (state.failed) return expr;
			// Parser.g:275:7: ( ( K_JSON selectClause )=> K_JSON )?
			int alt2=2;
			alt2 = dfa2.predict(input);
			switch (alt2) {
				case 1 :
					// Parser.g:275:9: ( K_JSON selectClause )=> K_JSON
					{
					match(input,K_JSON,FOLLOW_K_JSON_in_selectStatement1068); if (state.failed) return expr;
					if ( state.backtracking==0 ) { isJson = true; }
					}
					break;

			}

			pushFollow(FOLLOW_selectClause_in_selectStatement1077);
			sclause=selectClause();
			state._fsp--;
			if (state.failed) return expr;
			match(input,K_FROM,FOLLOW_K_FROM_in_selectStatement1085); if (state.failed) return expr;
			pushFollow(FOLLOW_columnFamilyName_in_selectStatement1089);
			cf=columnFamilyName();
			state._fsp--;
			if (state.failed) return expr;
			// Parser.g:277:7: ( K_WHERE wclause= whereClause )?
			int alt3=2;
			int LA3_0 = input.LA(1);
			if ( (LA3_0==K_WHERE) ) {
				alt3=1;
			}
			switch (alt3) {
				case 1 :
					// Parser.g:277:9: K_WHERE wclause= whereClause
					{
					match(input,K_WHERE,FOLLOW_K_WHERE_in_selectStatement1099); if (state.failed) return expr;
					pushFollow(FOLLOW_whereClause_in_selectStatement1103);
					wclause=whereClause();
					state._fsp--;
					if (state.failed) return expr;
					}
					break;

			}

			// Parser.g:278:7: ( K_GROUP K_BY groupByClause[groups] ( ',' groupByClause[groups] )* )?
			int alt5=2;
			int LA5_0 = input.LA(1);
			if ( (LA5_0==K_GROUP) ) {
				alt5=1;
			}
			switch (alt5) {
				case 1 :
					// Parser.g:278:9: K_GROUP K_BY groupByClause[groups] ( ',' groupByClause[groups] )*
					{
					match(input,K_GROUP,FOLLOW_K_GROUP_in_selectStatement1116); if (state.failed) return expr;
					match(input,K_BY,FOLLOW_K_BY_in_selectStatement1118); if (state.failed) return expr;
					pushFollow(FOLLOW_groupByClause_in_selectStatement1120);
					groupByClause(groups);
					state._fsp--;
					if (state.failed) return expr;
					// Parser.g:278:44: ( ',' groupByClause[groups] )*
					loop4:
					while (true) {
						int alt4=2;
						int LA4_0 = input.LA(1);
						if ( (LA4_0==194) ) {
							alt4=1;
						}

						switch (alt4) {
						case 1 :
							// Parser.g:278:46: ',' groupByClause[groups]
							{
							match(input,194,FOLLOW_194_in_selectStatement1125); if (state.failed) return expr;
							pushFollow(FOLLOW_groupByClause_in_selectStatement1127);
							groupByClause(groups);
							state._fsp--;
							if (state.failed) return expr;
							}
							break;

						default :
							break loop4;
						}
					}

					}
					break;

			}

			// Parser.g:279:7: ( K_ORDER K_BY orderByClause[orderings] ( ',' orderByClause[orderings] )* )?
			int alt7=2;
			int LA7_0 = input.LA(1);
			if ( (LA7_0==K_ORDER) ) {
				alt7=1;
			}
			switch (alt7) {
				case 1 :
					// Parser.g:279:9: K_ORDER K_BY orderByClause[orderings] ( ',' orderByClause[orderings] )*
					{
					match(input,K_ORDER,FOLLOW_K_ORDER_in_selectStatement1144); if (state.failed) return expr;
					match(input,K_BY,FOLLOW_K_BY_in_selectStatement1146); if (state.failed) return expr;
					pushFollow(FOLLOW_orderByClause_in_selectStatement1148);
					orderByClause(orderings);
					state._fsp--;
					if (state.failed) return expr;
					// Parser.g:279:47: ( ',' orderByClause[orderings] )*
					loop6:
					while (true) {
						int alt6=2;
						int LA6_0 = input.LA(1);
						if ( (LA6_0==194) ) {
							alt6=1;
						}

						switch (alt6) {
						case 1 :
							// Parser.g:279:49: ',' orderByClause[orderings]
							{
							match(input,194,FOLLOW_194_in_selectStatement1153); if (state.failed) return expr;
							pushFollow(FOLLOW_orderByClause_in_selectStatement1155);
							orderByClause(orderings);
							state._fsp--;
							if (state.failed) return expr;
							}
							break;

						default :
							break loop6;
						}
					}

					}
					break;

			}

			// Parser.g:280:7: ( K_PER K_PARTITION K_LIMIT rows= intValue )?
			int alt8=2;
			int LA8_0 = input.LA(1);
			if ( (LA8_0==K_PER) ) {
				alt8=1;
			}
			switch (alt8) {
				case 1 :
					// Parser.g:280:9: K_PER K_PARTITION K_LIMIT rows= intValue
					{
					match(input,K_PER,FOLLOW_K_PER_in_selectStatement1172); if (state.failed) return expr;
					match(input,K_PARTITION,FOLLOW_K_PARTITION_in_selectStatement1174); if (state.failed) return expr;
					match(input,K_LIMIT,FOLLOW_K_LIMIT_in_selectStatement1176); if (state.failed) return expr;
					pushFollow(FOLLOW_intValue_in_selectStatement1180);
					rows=intValue();
					state._fsp--;
					if (state.failed) return expr;
					if ( state.backtracking==0 ) { perPartitionLimit = rows; }
					}
					break;

			}

			// Parser.g:281:7: ( K_LIMIT rows= intValue )?
			int alt9=2;
			int LA9_0 = input.LA(1);
			if ( (LA9_0==K_LIMIT) ) {
				alt9=1;
			}
			switch (alt9) {
				case 1 :
					// Parser.g:281:9: K_LIMIT rows= intValue
					{
					match(input,K_LIMIT,FOLLOW_K_LIMIT_in_selectStatement1195); if (state.failed) return expr;
					pushFollow(FOLLOW_intValue_in_selectStatement1199);
					rows=intValue();
					state._fsp--;
					if (state.failed) return expr;
					if ( state.backtracking==0 ) { limit = rows; }
					}
					break;

			}

			// Parser.g:282:7: ( K_ALLOW K_FILTERING )?
			int alt10=2;
			int LA10_0 = input.LA(1);
			if ( (LA10_0==K_ALLOW) ) {
				alt10=1;
			}
			switch (alt10) {
				case 1 :
					// Parser.g:282:9: K_ALLOW K_FILTERING
					{
					match(input,K_ALLOW,FOLLOW_K_ALLOW_in_selectStatement1214); if (state.failed) return expr;
					match(input,K_FILTERING,FOLLOW_K_FILTERING_in_selectStatement1216); if (state.failed) return expr;
					if ( state.backtracking==0 ) { allowFiltering = true; }
					}
					break;

			}

			if ( state.backtracking==0 ) {
			          SelectStatement.Parameters params = new SelectStatement.Parameters(orderings,
			                                                                             groups,
			                                                                             (sclause!=null?((Cql_Parser.selectClause_return)sclause).isDistinct:false),
			                                                                             allowFiltering,
			                                                                             isJson);
			          WhereClause where = wclause == null ? WhereClause.empty() : wclause.build();
			          expr = new SelectStatement.RawStatement(cf, params, (sclause!=null?((Cql_Parser.selectClause_return)sclause).selectors:null), where, limit, perPartitionLimit);
			      }
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return expr;
	}
	// $ANTLR end "selectStatement"


	public static class selectClause_return extends ParserRuleReturnScope {
		public boolean isDistinct;
		public List<RawSelector> selectors;
	};


	// $ANTLR start "selectClause"
	// Parser.g:294:1: selectClause returns [boolean isDistinct, List<RawSelector> selectors] : ( ( K_DISTINCT selectors )=> K_DISTINCT s= selectors |s= selectors );
	public final Cql_Parser.selectClause_return selectClause() throws RecognitionException {
		Cql_Parser.selectClause_return retval = new Cql_Parser.selectClause_return();
		retval.start = input.LT(1);

		List<RawSelector> s =null;

		 retval.isDistinct = false; 
		try {
			// Parser.g:297:5: ( ( K_DISTINCT selectors )=> K_DISTINCT s= selectors |s= selectors )
			int alt11=2;
			alt11 = dfa11.predict(input);
			switch (alt11) {
				case 1 :
					// Parser.g:297:7: ( K_DISTINCT selectors )=> K_DISTINCT s= selectors
					{
					match(input,K_DISTINCT,FOLLOW_K_DISTINCT_in_selectClause1271); if (state.failed) return retval;
					pushFollow(FOLLOW_selectors_in_selectClause1275);
					s=selectors();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) { retval.isDistinct = true; retval.selectors = s; }
					}
					break;
				case 2 :
					// Parser.g:298:7: s= selectors
					{
					pushFollow(FOLLOW_selectors_in_selectClause1287);
					s=selectors();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) { retval.selectors = s; }
					}
					break;

			}
			retval.stop = input.LT(-1);

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "selectClause"



	// $ANTLR start "selectors"
	// Parser.g:301:1: selectors returns [List<RawSelector> expr] : (t1= selector ( ',' tN= selector )* | '\\*' );
	public final List<RawSelector> selectors() throws RecognitionException {
		List<RawSelector> expr = null;


		RawSelector t1 =null;
		RawSelector tN =null;

		try {
			// Parser.g:302:5: (t1= selector ( ',' tN= selector )* | '\\*' )
			int alt13=2;
			int LA13_0 = input.LA(1);
			if ( (LA13_0==BOOLEAN||LA13_0==DURATION||LA13_0==FLOAT||LA13_0==HEXNUMBER||(LA13_0 >= IDENT && LA13_0 <= INTEGER)||(LA13_0 >= K_AGGREGATE && LA13_0 <= K_ALL)||LA13_0==K_AS||LA13_0==K_ASCII||(LA13_0 >= K_BIGINT && LA13_0 <= K_BOOLEAN)||(LA13_0 >= K_CALLED && LA13_0 <= K_CLUSTERING)||(LA13_0 >= K_COMPACT && LA13_0 <= K_COUNTER)||LA13_0==K_CUSTOM||(LA13_0 >= K_DATE && LA13_0 <= K_DECIMAL)||(LA13_0 >= K_DISTINCT && LA13_0 <= K_DOUBLE)||LA13_0==K_DURATION||(LA13_0 >= K_EXISTS && LA13_0 <= K_FLOAT)||LA13_0==K_FROZEN||(LA13_0 >= K_FUNCTION && LA13_0 <= K_FUNCTIONS)||LA13_0==K_GROUP||(LA13_0 >= K_INET && LA13_0 <= K_INPUT)||LA13_0==K_INT||(LA13_0 >= K_JSON && LA13_0 <= K_KEYS)||(LA13_0 >= K_KEYSPACES && LA13_0 <= K_LIKE)||(LA13_0 >= K_LIST && LA13_0 <= K_MAP)||(LA13_0 >= K_NEGATIVE_INFINITY && LA13_0 <= K_NOLOGIN)||LA13_0==K_NOSUPERUSER||LA13_0==K_NULL||LA13_0==K_OPTIONS||(LA13_0 >= K_PARTITION && LA13_0 <= K_POSITIVE_NAN)||LA13_0==K_RETURNS||(LA13_0 >= K_ROLE && LA13_0 <= K_ROLES)||(LA13_0 >= K_SFUNC && LA13_0 <= K_TINYINT)||(LA13_0 >= K_TOKEN && LA13_0 <= K_TRIGGER)||(LA13_0 >= K_TTL && LA13_0 <= K_TYPE)||(LA13_0 >= K_USER && LA13_0 <= K_USERS)||(LA13_0 >= K_UUID && LA13_0 <= K_VARINT)||LA13_0==K_WRITETIME||(LA13_0 >= QMARK && LA13_0 <= QUOTED_NAME)||LA13_0==STRING_LITERAL||LA13_0==UUID||LA13_0==190||LA13_0==195||LA13_0==199||LA13_0==206||LA13_0==210) ) {
				alt13=1;
			}
			else if ( (LA13_0==207) ) {
				alt13=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return expr;}
				NoViableAltException nvae =
					new NoViableAltException("", 13, 0, input);
				throw nvae;
			}

			switch (alt13) {
				case 1 :
					// Parser.g:302:7: t1= selector ( ',' tN= selector )*
					{
					pushFollow(FOLLOW_selector_in_selectors1312);
					t1=selector();
					state._fsp--;
					if (state.failed) return expr;
					if ( state.backtracking==0 ) { expr = new ArrayList<RawSelector>(); expr.add(t1); }
					// Parser.g:302:76: ( ',' tN= selector )*
					loop12:
					while (true) {
						int alt12=2;
						int LA12_0 = input.LA(1);
						if ( (LA12_0==194) ) {
							alt12=1;
						}

						switch (alt12) {
						case 1 :
							// Parser.g:302:77: ',' tN= selector
							{
							match(input,194,FOLLOW_194_in_selectors1317); if (state.failed) return expr;
							pushFollow(FOLLOW_selector_in_selectors1321);
							tN=selector();
							state._fsp--;
							if (state.failed) return expr;
							if ( state.backtracking==0 ) { expr.add(tN); }
							}
							break;

						default :
							break loop12;
						}
					}

					}
					break;
				case 2 :
					// Parser.g:303:7: '\\*'
					{
					match(input,207,FOLLOW_207_in_selectors1333); if (state.failed) return expr;
					if ( state.backtracking==0 ) { expr = Collections.<RawSelector>emptyList();}
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return expr;
	}
	// $ANTLR end "selectors"



	// $ANTLR start "selector"
	// Parser.g:306:1: selector returns [RawSelector s] : us= unaliasedSelector ( K_AS c= noncol_ident )? ;
	public final RawSelector selector() throws RecognitionException {
		RawSelector s = null;


		Selectable.Raw us =null;
		ColumnIdentifier c =null;

		 ColumnIdentifier alias = null; 
		try {
			// Parser.g:308:5: (us= unaliasedSelector ( K_AS c= noncol_ident )? )
			// Parser.g:308:7: us= unaliasedSelector ( K_AS c= noncol_ident )?
			{
			pushFollow(FOLLOW_unaliasedSelector_in_selector1366);
			us=unaliasedSelector();
			state._fsp--;
			if (state.failed) return s;
			// Parser.g:308:28: ( K_AS c= noncol_ident )?
			int alt14=2;
			int LA14_0 = input.LA(1);
			if ( (LA14_0==K_AS) ) {
				alt14=1;
			}
			switch (alt14) {
				case 1 :
					// Parser.g:308:29: K_AS c= noncol_ident
					{
					match(input,K_AS,FOLLOW_K_AS_in_selector1369); if (state.failed) return s;
					pushFollow(FOLLOW_noncol_ident_in_selector1373);
					c=noncol_ident();
					state._fsp--;
					if (state.failed) return s;
					if ( state.backtracking==0 ) { alias = c; }
					}
					break;

			}

			if ( state.backtracking==0 ) { s = new RawSelector(us, alias); }
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return s;
	}
	// $ANTLR end "selector"



	// $ANTLR start "unaliasedSelector"
	// Parser.g:311:1: unaliasedSelector returns [Selectable.Raw s] : a= selectionAddition ;
	public final Selectable.Raw unaliasedSelector() throws RecognitionException {
		Selectable.Raw s = null;


		Selectable.Raw a =null;

		try {
			// Parser.g:312:5: (a= selectionAddition )
			// Parser.g:312:7: a= selectionAddition
			{
			pushFollow(FOLLOW_selectionAddition_in_unaliasedSelector1402);
			a=selectionAddition();
			state._fsp--;
			if (state.failed) return s;
			if ( state.backtracking==0 ) {s = a;}
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return s;
	}
	// $ANTLR end "unaliasedSelector"



	// $ANTLR start "selectionAddition"
	// Parser.g:315:1: selectionAddition returns [Selectable.Raw s] : l= selectionMultiplication ( '+' r= selectionMultiplication | '-' r= selectionMultiplication )* ;
	public final Selectable.Raw selectionAddition() throws RecognitionException {
		Selectable.Raw s = null;


		Selectable.Raw l =null;
		Selectable.Raw r =null;

		try {
			// Parser.g:316:5: (l= selectionMultiplication ( '+' r= selectionMultiplication | '-' r= selectionMultiplication )* )
			// Parser.g:316:9: l= selectionMultiplication ( '+' r= selectionMultiplication | '-' r= selectionMultiplication )*
			{
			pushFollow(FOLLOW_selectionMultiplication_in_selectionAddition1429);
			l=selectionMultiplication();
			state._fsp--;
			if (state.failed) return s;
			if ( state.backtracking==0 ) {s = l;}
			// Parser.g:317:9: ( '+' r= selectionMultiplication | '-' r= selectionMultiplication )*
			loop15:
			while (true) {
				int alt15=3;
				int LA15_0 = input.LA(1);
				if ( (LA15_0==192) ) {
					alt15=1;
				}
				else if ( (LA15_0==195) ) {
					alt15=2;
				}

				switch (alt15) {
				case 1 :
					// Parser.g:317:11: '+' r= selectionMultiplication
					{
					match(input,192,FOLLOW_192_in_selectionAddition1445); if (state.failed) return s;
					pushFollow(FOLLOW_selectionMultiplication_in_selectionAddition1449);
					r=selectionMultiplication();
					state._fsp--;
					if (state.failed) return s;
					if ( state.backtracking==0 ) {s = Selectable.WithFunction.Raw.newOperation('+', s, r);}
					}
					break;
				case 2 :
					// Parser.g:318:11: '-' r= selectionMultiplication
					{
					match(input,195,FOLLOW_195_in_selectionAddition1463); if (state.failed) return s;
					pushFollow(FOLLOW_selectionMultiplication_in_selectionAddition1467);
					r=selectionMultiplication();
					state._fsp--;
					if (state.failed) return s;
					if ( state.backtracking==0 ) {s = Selectable.WithFunction.Raw.newOperation('-', s, r);}
					}
					break;

				default :
					break loop15;
				}
			}

			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return s;
	}
	// $ANTLR end "selectionAddition"



	// $ANTLR start "selectionMultiplication"
	// Parser.g:322:1: selectionMultiplication returns [Selectable.Raw s] : l= selectionGroup ( '\\*' r= selectionGroup | '/' r= selectionGroup | '%' r= selectionGroup )* ;
	public final Selectable.Raw selectionMultiplication() throws RecognitionException {
		Selectable.Raw s = null;


		Selectable.Raw l =null;
		Selectable.Raw r =null;

		try {
			// Parser.g:323:5: (l= selectionGroup ( '\\*' r= selectionGroup | '/' r= selectionGroup | '%' r= selectionGroup )* )
			// Parser.g:323:9: l= selectionGroup ( '\\*' r= selectionGroup | '/' r= selectionGroup | '%' r= selectionGroup )*
			{
			pushFollow(FOLLOW_selectionGroup_in_selectionMultiplication1505);
			l=selectionGroup();
			state._fsp--;
			if (state.failed) return s;
			if ( state.backtracking==0 ) {s = l;}
			// Parser.g:324:9: ( '\\*' r= selectionGroup | '/' r= selectionGroup | '%' r= selectionGroup )*
			loop16:
			while (true) {
				int alt16=4;
				switch ( input.LA(1) ) {
				case 207:
					{
					alt16=1;
					}
					break;
				case 198:
					{
					alt16=2;
					}
					break;
				case 189:
					{
					alt16=3;
					}
					break;
				}
				switch (alt16) {
				case 1 :
					// Parser.g:324:11: '\\*' r= selectionGroup
					{
					match(input,207,FOLLOW_207_in_selectionMultiplication1521); if (state.failed) return s;
					pushFollow(FOLLOW_selectionGroup_in_selectionMultiplication1525);
					r=selectionGroup();
					state._fsp--;
					if (state.failed) return s;
					if ( state.backtracking==0 ) {s = Selectable.WithFunction.Raw.newOperation('*', s, r);}
					}
					break;
				case 2 :
					// Parser.g:325:11: '/' r= selectionGroup
					{
					match(input,198,FOLLOW_198_in_selectionMultiplication1539); if (state.failed) return s;
					pushFollow(FOLLOW_selectionGroup_in_selectionMultiplication1543);
					r=selectionGroup();
					state._fsp--;
					if (state.failed) return s;
					if ( state.backtracking==0 ) {s = Selectable.WithFunction.Raw.newOperation('/', s, r);}
					}
					break;
				case 3 :
					// Parser.g:326:11: '%' r= selectionGroup
					{
					match(input,189,FOLLOW_189_in_selectionMultiplication1557); if (state.failed) return s;
					pushFollow(FOLLOW_selectionGroup_in_selectionMultiplication1561);
					r=selectionGroup();
					state._fsp--;
					if (state.failed) return s;
					if ( state.backtracking==0 ) {s = Selectable.WithFunction.Raw.newOperation('%', s, r);}
					}
					break;

				default :
					break loop16;
				}
			}

			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return s;
	}
	// $ANTLR end "selectionMultiplication"



	// $ANTLR start "selectionGroup"
	// Parser.g:330:1: selectionGroup returns [Selectable.Raw s] : ( ( selectionGroupWithField )=>f= selectionGroupWithField |g= selectionGroupWithoutField | '-' g= selectionGroup );
	public final Selectable.Raw selectionGroup() throws RecognitionException {
		Selectable.Raw s = null;


		Selectable.Raw f =null;
		Selectable.Raw g =null;

		try {
			// Parser.g:331:5: ( ( selectionGroupWithField )=>f= selectionGroupWithField |g= selectionGroupWithoutField | '-' g= selectionGroup )
			int alt17=3;
			alt17 = dfa17.predict(input);
			switch (alt17) {
				case 1 :
					// Parser.g:331:7: ( selectionGroupWithField )=>f= selectionGroupWithField
					{
					pushFollow(FOLLOW_selectionGroupWithField_in_selectionGroup1603);
					f=selectionGroupWithField();
					state._fsp--;
					if (state.failed) return s;
					if ( state.backtracking==0 ) { s =f; }
					}
					break;
				case 2 :
					// Parser.g:332:7: g= selectionGroupWithoutField
					{
					pushFollow(FOLLOW_selectionGroupWithoutField_in_selectionGroup1615);
					g=selectionGroupWithoutField();
					state._fsp--;
					if (state.failed) return s;
					if ( state.backtracking==0 ) { s =g; }
					}
					break;
				case 3 :
					// Parser.g:333:7: '-' g= selectionGroup
					{
					match(input,195,FOLLOW_195_in_selectionGroup1625); if (state.failed) return s;
					pushFollow(FOLLOW_selectionGroup_in_selectionGroup1629);
					g=selectionGroup();
					state._fsp--;
					if (state.failed) return s;
					if ( state.backtracking==0 ) {s = Selectable.WithFunction.Raw.newNegation(g);}
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return s;
	}
	// $ANTLR end "selectionGroup"



	// $ANTLR start "selectionGroupWithField"
	// Parser.g:336:1: selectionGroupWithField returns [Selectable.Raw s] : g= selectionGroupWithoutField m= selectorModifier[g] ;
	public final Selectable.Raw selectionGroupWithField() throws RecognitionException {
		Selectable.Raw s = null;


		Selectable.Raw g =null;
		Selectable.Raw m =null;

		try {
			// Parser.g:337:5: (g= selectionGroupWithoutField m= selectorModifier[g] )
			// Parser.g:337:7: g= selectionGroupWithoutField m= selectorModifier[g]
			{
			pushFollow(FOLLOW_selectionGroupWithoutField_in_selectionGroupWithField1654);
			g=selectionGroupWithoutField();
			state._fsp--;
			if (state.failed) return s;
			pushFollow(FOLLOW_selectorModifier_in_selectionGroupWithField1658);
			m=selectorModifier(g);
			state._fsp--;
			if (state.failed) return s;
			if ( state.backtracking==0 ) {s = m;}
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return s;
	}
	// $ANTLR end "selectionGroupWithField"



	// $ANTLR start "selectorModifier"
	// Parser.g:340:1: selectorModifier[Selectable.Raw receiver] returns [Selectable.Raw s] : (f= fieldSelectorModifier[receiver] m= selectorModifier[f] | '[' ss= collectionSubSelection[receiver] ']' m= selectorModifier[ss] |);
	public final Selectable.Raw selectorModifier(Selectable.Raw receiver) throws RecognitionException {
		Selectable.Raw s = null;


		Selectable.Raw f =null;
		Selectable.Raw m =null;
		Selectable.Raw ss =null;

		try {
			// Parser.g:341:5: (f= fieldSelectorModifier[receiver] m= selectorModifier[f] | '[' ss= collectionSubSelection[receiver] ']' m= selectorModifier[ss] |)
			int alt18=3;
			switch ( input.LA(1) ) {
			case 197:
				{
				alt18=1;
				}
				break;
			case 206:
				{
				alt18=2;
				}
				break;
			case EOF:
			case K_AS:
			case K_FROM:
			case 189:
			case 191:
			case 192:
			case 194:
			case 195:
			case 198:
			case 199:
			case 207:
			case 208:
			case 211:
				{
				alt18=3;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return s;}
				NoViableAltException nvae =
					new NoViableAltException("", 18, 0, input);
				throw nvae;
			}
			switch (alt18) {
				case 1 :
					// Parser.g:341:7: f= fieldSelectorModifier[receiver] m= selectorModifier[f]
					{
					pushFollow(FOLLOW_fieldSelectorModifier_in_selectorModifier1685);
					f=fieldSelectorModifier(receiver);
					state._fsp--;
					if (state.failed) return s;
					pushFollow(FOLLOW_selectorModifier_in_selectorModifier1690);
					m=selectorModifier(f);
					state._fsp--;
					if (state.failed) return s;
					if ( state.backtracking==0 ) { s = m; }
					}
					break;
				case 2 :
					// Parser.g:342:7: '[' ss= collectionSubSelection[receiver] ']' m= selectorModifier[ss]
					{
					match(input,206,FOLLOW_206_in_selectorModifier1701); if (state.failed) return s;
					pushFollow(FOLLOW_collectionSubSelection_in_selectorModifier1705);
					ss=collectionSubSelection(receiver);
					state._fsp--;
					if (state.failed) return s;
					match(input,208,FOLLOW_208_in_selectorModifier1708); if (state.failed) return s;
					pushFollow(FOLLOW_selectorModifier_in_selectorModifier1712);
					m=selectorModifier(ss);
					state._fsp--;
					if (state.failed) return s;
					if ( state.backtracking==0 ) { s = m; }
					}
					break;
				case 3 :
					// Parser.g:343:7: 
					{
					if ( state.backtracking==0 ) { s = receiver; }
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return s;
	}
	// $ANTLR end "selectorModifier"



	// $ANTLR start "fieldSelectorModifier"
	// Parser.g:346:1: fieldSelectorModifier[Selectable.Raw receiver] returns [Selectable.Raw s] : '.' fi= fident ;
	public final Selectable.Raw fieldSelectorModifier(Selectable.Raw receiver) throws RecognitionException {
		Selectable.Raw s = null;


		FieldIdentifier fi =null;

		try {
			// Parser.g:347:5: ( '.' fi= fident )
			// Parser.g:347:7: '.' fi= fident
			{
			match(input,197,FOLLOW_197_in_fieldSelectorModifier1745); if (state.failed) return s;
			pushFollow(FOLLOW_fident_in_fieldSelectorModifier1749);
			fi=fident();
			state._fsp--;
			if (state.failed) return s;
			if ( state.backtracking==0 ) { s = new Selectable.WithFieldSelection.Raw(receiver, fi); }
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return s;
	}
	// $ANTLR end "fieldSelectorModifier"



	// $ANTLR start "collectionSubSelection"
	// Parser.g:350:1: collectionSubSelection[Selectable.Raw receiver] returns [Selectable.Raw s] : (t1= term ( RANGE (t2= term )? )? | RANGE t2= term ) ;
	public final Selectable.Raw collectionSubSelection(Selectable.Raw receiver) throws RecognitionException {
		Selectable.Raw s = null;


		Term.Raw t1 =null;
		Term.Raw t2 =null;

		 boolean isSlice=false; 
		try {
			// Parser.g:352:5: ( (t1= term ( RANGE (t2= term )? )? | RANGE t2= term ) )
			// Parser.g:352:7: (t1= term ( RANGE (t2= term )? )? | RANGE t2= term )
			{
			// Parser.g:352:7: (t1= term ( RANGE (t2= term )? )? | RANGE t2= term )
			int alt21=2;
			int LA21_0 = input.LA(1);
			if ( (LA21_0==BOOLEAN||LA21_0==DURATION||LA21_0==FLOAT||LA21_0==HEXNUMBER||(LA21_0 >= IDENT && LA21_0 <= INTEGER)||(LA21_0 >= K_AGGREGATE && LA21_0 <= K_ALL)||LA21_0==K_AS||LA21_0==K_ASCII||(LA21_0 >= K_BIGINT && LA21_0 <= K_BOOLEAN)||(LA21_0 >= K_CALLED && LA21_0 <= K_CLUSTERING)||(LA21_0 >= K_COMPACT && LA21_0 <= K_COUNTER)||LA21_0==K_CUSTOM||(LA21_0 >= K_DATE && LA21_0 <= K_DECIMAL)||(LA21_0 >= K_DISTINCT && LA21_0 <= K_DOUBLE)||LA21_0==K_DURATION||(LA21_0 >= K_EXISTS && LA21_0 <= K_FLOAT)||LA21_0==K_FROZEN||(LA21_0 >= K_FUNCTION && LA21_0 <= K_FUNCTIONS)||LA21_0==K_GROUP||(LA21_0 >= K_INET && LA21_0 <= K_INPUT)||LA21_0==K_INT||(LA21_0 >= K_JSON && LA21_0 <= K_KEYS)||(LA21_0 >= K_KEYSPACES && LA21_0 <= K_LIKE)||(LA21_0 >= K_LIST && LA21_0 <= K_MAP)||(LA21_0 >= K_NEGATIVE_INFINITY && LA21_0 <= K_NOLOGIN)||LA21_0==K_NOSUPERUSER||LA21_0==K_NULL||LA21_0==K_OPTIONS||(LA21_0 >= K_PARTITION && LA21_0 <= K_POSITIVE_NAN)||LA21_0==K_RETURNS||(LA21_0 >= K_ROLE && LA21_0 <= K_ROLES)||(LA21_0 >= K_SFUNC && LA21_0 <= K_TINYINT)||(LA21_0 >= K_TOKEN && LA21_0 <= K_TRIGGER)||(LA21_0 >= K_TTL && LA21_0 <= K_TYPE)||(LA21_0 >= K_USER && LA21_0 <= K_USERS)||(LA21_0 >= K_UUID && LA21_0 <= K_VARINT)||LA21_0==K_WRITETIME||(LA21_0 >= QMARK && LA21_0 <= QUOTED_NAME)||LA21_0==STRING_LITERAL||LA21_0==UUID||LA21_0==190||LA21_0==195||LA21_0==199||LA21_0==206||LA21_0==210) ) {
				alt21=1;
			}
			else if ( (LA21_0==RANGE) ) {
				alt21=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return s;}
				NoViableAltException nvae =
					new NoViableAltException("", 21, 0, input);
				throw nvae;
			}

			switch (alt21) {
				case 1 :
					// Parser.g:352:9: t1= term ( RANGE (t2= term )? )?
					{
					pushFollow(FOLLOW_term_in_collectionSubSelection1787);
					t1=term();
					state._fsp--;
					if (state.failed) return s;
					// Parser.g:352:17: ( RANGE (t2= term )? )?
					int alt20=2;
					int LA20_0 = input.LA(1);
					if ( (LA20_0==RANGE) ) {
						alt20=1;
					}
					switch (alt20) {
						case 1 :
							// Parser.g:352:19: RANGE (t2= term )?
							{
							if ( state.backtracking==0 ) { isSlice=true; }
							match(input,RANGE,FOLLOW_RANGE_in_collectionSubSelection1793); if (state.failed) return s;
							// Parser.g:352:43: (t2= term )?
							int alt19=2;
							int LA19_0 = input.LA(1);
							if ( (LA19_0==BOOLEAN||LA19_0==DURATION||LA19_0==FLOAT||LA19_0==HEXNUMBER||(LA19_0 >= IDENT && LA19_0 <= INTEGER)||(LA19_0 >= K_AGGREGATE && LA19_0 <= K_ALL)||LA19_0==K_AS||LA19_0==K_ASCII||(LA19_0 >= K_BIGINT && LA19_0 <= K_BOOLEAN)||(LA19_0 >= K_CALLED && LA19_0 <= K_CLUSTERING)||(LA19_0 >= K_COMPACT && LA19_0 <= K_COUNTER)||LA19_0==K_CUSTOM||(LA19_0 >= K_DATE && LA19_0 <= K_DECIMAL)||(LA19_0 >= K_DISTINCT && LA19_0 <= K_DOUBLE)||LA19_0==K_DURATION||(LA19_0 >= K_EXISTS && LA19_0 <= K_FLOAT)||LA19_0==K_FROZEN||(LA19_0 >= K_FUNCTION && LA19_0 <= K_FUNCTIONS)||LA19_0==K_GROUP||(LA19_0 >= K_INET && LA19_0 <= K_INPUT)||LA19_0==K_INT||(LA19_0 >= K_JSON && LA19_0 <= K_KEYS)||(LA19_0 >= K_KEYSPACES && LA19_0 <= K_LIKE)||(LA19_0 >= K_LIST && LA19_0 <= K_MAP)||(LA19_0 >= K_NEGATIVE_INFINITY && LA19_0 <= K_NOLOGIN)||LA19_0==K_NOSUPERUSER||LA19_0==K_NULL||LA19_0==K_OPTIONS||(LA19_0 >= K_PARTITION && LA19_0 <= K_POSITIVE_NAN)||LA19_0==K_RETURNS||(LA19_0 >= K_ROLE && LA19_0 <= K_ROLES)||(LA19_0 >= K_SFUNC && LA19_0 <= K_TINYINT)||(LA19_0 >= K_TOKEN && LA19_0 <= K_TRIGGER)||(LA19_0 >= K_TTL && LA19_0 <= K_TYPE)||(LA19_0 >= K_USER && LA19_0 <= K_USERS)||(LA19_0 >= K_UUID && LA19_0 <= K_VARINT)||LA19_0==K_WRITETIME||(LA19_0 >= QMARK && LA19_0 <= QUOTED_NAME)||LA19_0==STRING_LITERAL||LA19_0==UUID||LA19_0==190||LA19_0==195||LA19_0==199||LA19_0==206||LA19_0==210) ) {
								alt19=1;
							}
							switch (alt19) {
								case 1 :
									// Parser.g:352:44: t2= term
									{
									pushFollow(FOLLOW_term_in_collectionSubSelection1798);
									t2=term();
									state._fsp--;
									if (state.failed) return s;
									}
									break;

							}

							}
							break;

					}

					}
					break;
				case 2 :
					// Parser.g:353:9: RANGE t2= term
					{
					match(input,RANGE,FOLLOW_RANGE_in_collectionSubSelection1813); if (state.failed) return s;
					if ( state.backtracking==0 ) { isSlice=true; }
					pushFollow(FOLLOW_term_in_collectionSubSelection1819);
					t2=term();
					state._fsp--;
					if (state.failed) return s;
					}
					break;

			}

			if ( state.backtracking==0 ) {
			          s = isSlice
			             ? new Selectable.WithSliceSelection.Raw(receiver, t1, t2)
			             : new Selectable.WithElementSelection.Raw(receiver, t1);
			      }
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return s;
	}
	// $ANTLR end "collectionSubSelection"



	// $ANTLR start "selectionGroupWithoutField"
	// Parser.g:361:1: selectionGroupWithoutField returns [Selectable.Raw s] : (sn= simpleUnaliasedSelector | ( selectionTypeHint )=>h= selectionTypeHint |t= selectionTupleOrNestedSelector |l= selectionList |m= selectionMapOrSet );
	public final Selectable.Raw selectionGroupWithoutField() throws RecognitionException {
		Selectable.Raw s = null;


		Selectable.Raw sn =null;
		Selectable.Raw h =null;
		Selectable.Raw t =null;
		Selectable.Raw l =null;
		Selectable.Raw m =null;

		 Selectable.Raw tmp = null; 
		try {
			// Parser.g:364:5: (sn= simpleUnaliasedSelector | ( selectionTypeHint )=>h= selectionTypeHint |t= selectionTupleOrNestedSelector |l= selectionList |m= selectionMapOrSet )
			int alt22=5;
			alt22 = dfa22.predict(input);
			switch (alt22) {
				case 1 :
					// Parser.g:364:7: sn= simpleUnaliasedSelector
					{
					pushFollow(FOLLOW_simpleUnaliasedSelector_in_selectionGroupWithoutField1871);
					sn=simpleUnaliasedSelector();
					state._fsp--;
					if (state.failed) return s;
					if ( state.backtracking==0 ) { tmp=sn; }
					}
					break;
				case 2 :
					// Parser.g:365:7: ( selectionTypeHint )=>h= selectionTypeHint
					{
					pushFollow(FOLLOW_selectionTypeHint_in_selectionGroupWithoutField1889);
					h=selectionTypeHint();
					state._fsp--;
					if (state.failed) return s;
					if ( state.backtracking==0 ) { tmp=h; }
					}
					break;
				case 3 :
					// Parser.g:366:7: t= selectionTupleOrNestedSelector
					{
					pushFollow(FOLLOW_selectionTupleOrNestedSelector_in_selectionGroupWithoutField1901);
					t=selectionTupleOrNestedSelector();
					state._fsp--;
					if (state.failed) return s;
					if ( state.backtracking==0 ) { tmp=t; }
					}
					break;
				case 4 :
					// Parser.g:367:7: l= selectionList
					{
					pushFollow(FOLLOW_selectionList_in_selectionGroupWithoutField1913);
					l=selectionList();
					state._fsp--;
					if (state.failed) return s;
					if ( state.backtracking==0 ) { tmp=l; }
					}
					break;
				case 5 :
					// Parser.g:368:7: m= selectionMapOrSet
					{
					pushFollow(FOLLOW_selectionMapOrSet_in_selectionGroupWithoutField1925);
					m=selectionMapOrSet();
					state._fsp--;
					if (state.failed) return s;
					if ( state.backtracking==0 ) { tmp=m; }
					}
					break;

			}
			if ( state.backtracking==0 ) { s = tmp; }
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return s;
	}
	// $ANTLR end "selectionGroupWithoutField"



	// $ANTLR start "selectionTypeHint"
	// Parser.g:372:1: selectionTypeHint returns [Selectable.Raw s] : '(' ct= comparatorType ')' a= selectionGroupWithoutField ;
	public final Selectable.Raw selectionTypeHint() throws RecognitionException {
		Selectable.Raw s = null;


		CQL3Type.Raw ct =null;
		Selectable.Raw a =null;

		try {
			// Parser.g:373:5: ( '(' ct= comparatorType ')' a= selectionGroupWithoutField )
			// Parser.g:373:7: '(' ct= comparatorType ')' a= selectionGroupWithoutField
			{
			match(input,190,FOLLOW_190_in_selectionTypeHint1953); if (state.failed) return s;
			pushFollow(FOLLOW_comparatorType_in_selectionTypeHint1957);
			ct=comparatorType();
			state._fsp--;
			if (state.failed) return s;
			match(input,191,FOLLOW_191_in_selectionTypeHint1959); if (state.failed) return s;
			pushFollow(FOLLOW_selectionGroupWithoutField_in_selectionTypeHint1963);
			a=selectionGroupWithoutField();
			state._fsp--;
			if (state.failed) return s;
			if ( state.backtracking==0 ) { s = new Selectable.WithTypeHint.Raw(ct, a); }
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return s;
	}
	// $ANTLR end "selectionTypeHint"



	// $ANTLR start "selectionList"
	// Parser.g:376:1: selectionList returns [Selectable.Raw s] : '[' (t1= unaliasedSelector ( ',' tn= unaliasedSelector )* )? ']' ;
	public final Selectable.Raw selectionList() throws RecognitionException {
		Selectable.Raw s = null;


		Selectable.Raw t1 =null;
		Selectable.Raw tn =null;

		 List<Selectable.Raw> l = new ArrayList<>(); 
		try {
			// Parser.g:379:5: ( '[' (t1= unaliasedSelector ( ',' tn= unaliasedSelector )* )? ']' )
			// Parser.g:379:7: '[' (t1= unaliasedSelector ( ',' tn= unaliasedSelector )* )? ']'
			{
			match(input,206,FOLLOW_206_in_selectionList2004); if (state.failed) return s;
			// Parser.g:379:11: (t1= unaliasedSelector ( ',' tn= unaliasedSelector )* )?
			int alt24=2;
			int LA24_0 = input.LA(1);
			if ( (LA24_0==BOOLEAN||LA24_0==DURATION||LA24_0==FLOAT||LA24_0==HEXNUMBER||(LA24_0 >= IDENT && LA24_0 <= INTEGER)||(LA24_0 >= K_AGGREGATE && LA24_0 <= K_ALL)||LA24_0==K_AS||LA24_0==K_ASCII||(LA24_0 >= K_BIGINT && LA24_0 <= K_BOOLEAN)||(LA24_0 >= K_CALLED && LA24_0 <= K_CLUSTERING)||(LA24_0 >= K_COMPACT && LA24_0 <= K_COUNTER)||LA24_0==K_CUSTOM||(LA24_0 >= K_DATE && LA24_0 <= K_DECIMAL)||(LA24_0 >= K_DISTINCT && LA24_0 <= K_DOUBLE)||LA24_0==K_DURATION||(LA24_0 >= K_EXISTS && LA24_0 <= K_FLOAT)||LA24_0==K_FROZEN||(LA24_0 >= K_FUNCTION && LA24_0 <= K_FUNCTIONS)||LA24_0==K_GROUP||(LA24_0 >= K_INET && LA24_0 <= K_INPUT)||LA24_0==K_INT||(LA24_0 >= K_JSON && LA24_0 <= K_KEYS)||(LA24_0 >= K_KEYSPACES && LA24_0 <= K_LIKE)||(LA24_0 >= K_LIST && LA24_0 <= K_MAP)||(LA24_0 >= K_NEGATIVE_INFINITY && LA24_0 <= K_NOLOGIN)||LA24_0==K_NOSUPERUSER||LA24_0==K_NULL||LA24_0==K_OPTIONS||(LA24_0 >= K_PARTITION && LA24_0 <= K_POSITIVE_NAN)||LA24_0==K_RETURNS||(LA24_0 >= K_ROLE && LA24_0 <= K_ROLES)||(LA24_0 >= K_SFUNC && LA24_0 <= K_TINYINT)||(LA24_0 >= K_TOKEN && LA24_0 <= K_TRIGGER)||(LA24_0 >= K_TTL && LA24_0 <= K_TYPE)||(LA24_0 >= K_USER && LA24_0 <= K_USERS)||(LA24_0 >= K_UUID && LA24_0 <= K_VARINT)||LA24_0==K_WRITETIME||(LA24_0 >= QMARK && LA24_0 <= QUOTED_NAME)||LA24_0==STRING_LITERAL||LA24_0==UUID||LA24_0==190||LA24_0==195||LA24_0==199||LA24_0==206||LA24_0==210) ) {
				alt24=1;
			}
			switch (alt24) {
				case 1 :
					// Parser.g:379:13: t1= unaliasedSelector ( ',' tn= unaliasedSelector )*
					{
					pushFollow(FOLLOW_unaliasedSelector_in_selectionList2010);
					t1=unaliasedSelector();
					state._fsp--;
					if (state.failed) return s;
					if ( state.backtracking==0 ) { l.add(t1); }
					// Parser.g:379:49: ( ',' tn= unaliasedSelector )*
					loop23:
					while (true) {
						int alt23=2;
						int LA23_0 = input.LA(1);
						if ( (LA23_0==194) ) {
							alt23=1;
						}

						switch (alt23) {
						case 1 :
							// Parser.g:379:51: ',' tn= unaliasedSelector
							{
							match(input,194,FOLLOW_194_in_selectionList2016); if (state.failed) return s;
							pushFollow(FOLLOW_unaliasedSelector_in_selectionList2020);
							tn=unaliasedSelector();
							state._fsp--;
							if (state.failed) return s;
							if ( state.backtracking==0 ) { l.add(tn); }
							}
							break;

						default :
							break loop23;
						}
					}

					}
					break;

			}

			match(input,208,FOLLOW_208_in_selectionList2030); if (state.failed) return s;
			}

			if ( state.backtracking==0 ) { s = new Selectable.WithList.Raw(l); }
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return s;
	}
	// $ANTLR end "selectionList"



	// $ANTLR start "selectionMapOrSet"
	// Parser.g:382:1: selectionMapOrSet returns [Selectable.Raw s] : ( '{' t1= unaliasedSelector (m= selectionMap[t1] |st= selectionSet[t1] ) '}' | '{' '}' );
	public final Selectable.Raw selectionMapOrSet() throws RecognitionException {
		Selectable.Raw s = null;


		Selectable.Raw t1 =null;
		Selectable.Raw m =null;
		Selectable.Raw st =null;

		try {
			// Parser.g:383:5: ( '{' t1= unaliasedSelector (m= selectionMap[t1] |st= selectionSet[t1] ) '}' | '{' '}' )
			int alt26=2;
			int LA26_0 = input.LA(1);
			if ( (LA26_0==210) ) {
				int LA26_1 = input.LA(2);
				if ( (LA26_1==211) ) {
					alt26=2;
				}
				else if ( (LA26_1==BOOLEAN||LA26_1==DURATION||LA26_1==FLOAT||LA26_1==HEXNUMBER||(LA26_1 >= IDENT && LA26_1 <= INTEGER)||(LA26_1 >= K_AGGREGATE && LA26_1 <= K_ALL)||LA26_1==K_AS||LA26_1==K_ASCII||(LA26_1 >= K_BIGINT && LA26_1 <= K_BOOLEAN)||(LA26_1 >= K_CALLED && LA26_1 <= K_CLUSTERING)||(LA26_1 >= K_COMPACT && LA26_1 <= K_COUNTER)||LA26_1==K_CUSTOM||(LA26_1 >= K_DATE && LA26_1 <= K_DECIMAL)||(LA26_1 >= K_DISTINCT && LA26_1 <= K_DOUBLE)||LA26_1==K_DURATION||(LA26_1 >= K_EXISTS && LA26_1 <= K_FLOAT)||LA26_1==K_FROZEN||(LA26_1 >= K_FUNCTION && LA26_1 <= K_FUNCTIONS)||LA26_1==K_GROUP||(LA26_1 >= K_INET && LA26_1 <= K_INPUT)||LA26_1==K_INT||(LA26_1 >= K_JSON && LA26_1 <= K_KEYS)||(LA26_1 >= K_KEYSPACES && LA26_1 <= K_LIKE)||(LA26_1 >= K_LIST && LA26_1 <= K_MAP)||(LA26_1 >= K_NEGATIVE_INFINITY && LA26_1 <= K_NOLOGIN)||LA26_1==K_NOSUPERUSER||LA26_1==K_NULL||LA26_1==K_OPTIONS||(LA26_1 >= K_PARTITION && LA26_1 <= K_POSITIVE_NAN)||LA26_1==K_RETURNS||(LA26_1 >= K_ROLE && LA26_1 <= K_ROLES)||(LA26_1 >= K_SFUNC && LA26_1 <= K_TINYINT)||(LA26_1 >= K_TOKEN && LA26_1 <= K_TRIGGER)||(LA26_1 >= K_TTL && LA26_1 <= K_TYPE)||(LA26_1 >= K_USER && LA26_1 <= K_USERS)||(LA26_1 >= K_UUID && LA26_1 <= K_VARINT)||LA26_1==K_WRITETIME||(LA26_1 >= QMARK && LA26_1 <= QUOTED_NAME)||LA26_1==STRING_LITERAL||LA26_1==UUID||LA26_1==190||LA26_1==195||LA26_1==199||LA26_1==206||LA26_1==210) ) {
					alt26=1;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return s;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 26, 1, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

			}

			else {
				if (state.backtracking>0) {state.failed=true; return s;}
				NoViableAltException nvae =
					new NoViableAltException("", 26, 0, input);
				throw nvae;
			}

			switch (alt26) {
				case 1 :
					// Parser.g:383:7: '{' t1= unaliasedSelector (m= selectionMap[t1] |st= selectionSet[t1] ) '}'
					{
					match(input,210,FOLLOW_210_in_selectionMapOrSet2051); if (state.failed) return s;
					pushFollow(FOLLOW_unaliasedSelector_in_selectionMapOrSet2055);
					t1=unaliasedSelector();
					state._fsp--;
					if (state.failed) return s;
					// Parser.g:383:32: (m= selectionMap[t1] |st= selectionSet[t1] )
					int alt25=2;
					int LA25_0 = input.LA(1);
					if ( (LA25_0==199) ) {
						alt25=1;
					}
					else if ( (LA25_0==194||LA25_0==211) ) {
						alt25=2;
					}

					else {
						if (state.backtracking>0) {state.failed=true; return s;}
						NoViableAltException nvae =
							new NoViableAltException("", 25, 0, input);
						throw nvae;
					}

					switch (alt25) {
						case 1 :
							// Parser.g:383:34: m= selectionMap[t1]
							{
							pushFollow(FOLLOW_selectionMap_in_selectionMapOrSet2061);
							m=selectionMap(t1);
							state._fsp--;
							if (state.failed) return s;
							if ( state.backtracking==0 ) { s = m; }
							}
							break;
						case 2 :
							// Parser.g:383:67: st= selectionSet[t1]
							{
							pushFollow(FOLLOW_selectionSet_in_selectionMapOrSet2070);
							st=selectionSet(t1);
							state._fsp--;
							if (state.failed) return s;
							if ( state.backtracking==0 ) { s = st; }
							}
							break;

					}

					match(input,211,FOLLOW_211_in_selectionMapOrSet2076); if (state.failed) return s;
					}
					break;
				case 2 :
					// Parser.g:384:7: '{' '}'
					{
					match(input,210,FOLLOW_210_in_selectionMapOrSet2084); if (state.failed) return s;
					match(input,211,FOLLOW_211_in_selectionMapOrSet2086); if (state.failed) return s;
					if ( state.backtracking==0 ) { s = new Selectable.WithSet.Raw(Collections.emptyList());}
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return s;
	}
	// $ANTLR end "selectionMapOrSet"



	// $ANTLR start "selectionMap"
	// Parser.g:387:1: selectionMap[Selectable.Raw k1] returns [Selectable.Raw s] : ':' v1= unaliasedSelector ( ',' kn= unaliasedSelector ':' vn= unaliasedSelector )* ;
	public final Selectable.Raw selectionMap(Selectable.Raw k1) throws RecognitionException {
		Selectable.Raw s = null;


		Selectable.Raw v1 =null;
		Selectable.Raw kn =null;
		Selectable.Raw vn =null;

		 List<Pair<Selectable.Raw, Selectable.Raw>> m = new ArrayList<>(); 
		try {
			// Parser.g:390:7: ( ':' v1= unaliasedSelector ( ',' kn= unaliasedSelector ':' vn= unaliasedSelector )* )
			// Parser.g:390:9: ':' v1= unaliasedSelector ( ',' kn= unaliasedSelector ':' vn= unaliasedSelector )*
			{
			match(input,199,FOLLOW_199_in_selectionMap2131); if (state.failed) return s;
			pushFollow(FOLLOW_unaliasedSelector_in_selectionMap2135);
			v1=unaliasedSelector();
			state._fsp--;
			if (state.failed) return s;
			if ( state.backtracking==0 ) { m.add(Pair.create(k1, v1)); }
			// Parser.g:390:68: ( ',' kn= unaliasedSelector ':' vn= unaliasedSelector )*
			loop27:
			while (true) {
				int alt27=2;
				int LA27_0 = input.LA(1);
				if ( (LA27_0==194) ) {
					alt27=1;
				}

				switch (alt27) {
				case 1 :
					// Parser.g:390:70: ',' kn= unaliasedSelector ':' vn= unaliasedSelector
					{
					match(input,194,FOLLOW_194_in_selectionMap2143); if (state.failed) return s;
					pushFollow(FOLLOW_unaliasedSelector_in_selectionMap2147);
					kn=unaliasedSelector();
					state._fsp--;
					if (state.failed) return s;
					match(input,199,FOLLOW_199_in_selectionMap2149); if (state.failed) return s;
					pushFollow(FOLLOW_unaliasedSelector_in_selectionMap2153);
					vn=unaliasedSelector();
					state._fsp--;
					if (state.failed) return s;
					if ( state.backtracking==0 ) { m.add(Pair.create(kn, vn)); }
					}
					break;

				default :
					break loop27;
				}
			}

			}

			if ( state.backtracking==0 ) { s = new Selectable.WithMapOrUdt.Raw(m); }
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return s;
	}
	// $ANTLR end "selectionMap"



	// $ANTLR start "selectionSet"
	// Parser.g:393:1: selectionSet[Selectable.Raw t1] returns [Selectable.Raw s] : ( ',' tn= unaliasedSelector )* ;
	public final Selectable.Raw selectionSet(Selectable.Raw t1) throws RecognitionException {
		Selectable.Raw s = null;


		Selectable.Raw tn =null;

		 List<Selectable.Raw> l = new ArrayList<>(); l.add(t1); 
		try {
			// Parser.g:396:7: ( ( ',' tn= unaliasedSelector )* )
			// Parser.g:396:9: ( ',' tn= unaliasedSelector )*
			{
			// Parser.g:396:9: ( ',' tn= unaliasedSelector )*
			loop28:
			while (true) {
				int alt28=2;
				int LA28_0 = input.LA(1);
				if ( (LA28_0==194) ) {
					alt28=1;
				}

				switch (alt28) {
				case 1 :
					// Parser.g:396:11: ',' tn= unaliasedSelector
					{
					match(input,194,FOLLOW_194_in_selectionSet2205); if (state.failed) return s;
					pushFollow(FOLLOW_unaliasedSelector_in_selectionSet2209);
					tn=unaliasedSelector();
					state._fsp--;
					if (state.failed) return s;
					if ( state.backtracking==0 ) { l.add(tn); }
					}
					break;

				default :
					break loop28;
				}
			}

			}

			if ( state.backtracking==0 ) { s = new Selectable.WithSet.Raw(l); }
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return s;
	}
	// $ANTLR end "selectionSet"



	// $ANTLR start "selectionTupleOrNestedSelector"
	// Parser.g:399:1: selectionTupleOrNestedSelector returns [Selectable.Raw s] : '(' t1= unaliasedSelector ( ',' tn= unaliasedSelector )* ')' ;
	public final Selectable.Raw selectionTupleOrNestedSelector() throws RecognitionException {
		Selectable.Raw s = null;


		Selectable.Raw t1 =null;
		Selectable.Raw tn =null;

		 List<Selectable.Raw> l = new ArrayList<>(); 
		try {
			// Parser.g:402:5: ( '(' t1= unaliasedSelector ( ',' tn= unaliasedSelector )* ')' )
			// Parser.g:402:7: '(' t1= unaliasedSelector ( ',' tn= unaliasedSelector )* ')'
			{
			match(input,190,FOLLOW_190_in_selectionTupleOrNestedSelector2255); if (state.failed) return s;
			pushFollow(FOLLOW_unaliasedSelector_in_selectionTupleOrNestedSelector2259);
			t1=unaliasedSelector();
			state._fsp--;
			if (state.failed) return s;
			if ( state.backtracking==0 ) { l.add(t1); }
			// Parser.g:402:47: ( ',' tn= unaliasedSelector )*
			loop29:
			while (true) {
				int alt29=2;
				int LA29_0 = input.LA(1);
				if ( (LA29_0==194) ) {
					alt29=1;
				}

				switch (alt29) {
				case 1 :
					// Parser.g:402:48: ',' tn= unaliasedSelector
					{
					match(input,194,FOLLOW_194_in_selectionTupleOrNestedSelector2264); if (state.failed) return s;
					pushFollow(FOLLOW_unaliasedSelector_in_selectionTupleOrNestedSelector2268);
					tn=unaliasedSelector();
					state._fsp--;
					if (state.failed) return s;
					if ( state.backtracking==0 ) { l.add(tn); }
					}
					break;

				default :
					break loop29;
				}
			}

			match(input,191,FOLLOW_191_in_selectionTupleOrNestedSelector2275); if (state.failed) return s;
			}

			if ( state.backtracking==0 ) { s = new Selectable.BetweenParenthesesOrWithTuple.Raw(l); }
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return s;
	}
	// $ANTLR end "selectionTupleOrNestedSelector"



	// $ANTLR start "simpleUnaliasedSelector"
	// Parser.g:409:1: simpleUnaliasedSelector returns [Selectable.Raw s] : (c= sident |l= selectionLiteral |f= selectionFunction );
	public final Selectable.Raw simpleUnaliasedSelector() throws RecognitionException {
		Selectable.Raw s = null;


		Selectable.Raw c =null;
		Term.Raw l =null;
		Selectable.Raw f =null;

		try {
			// Parser.g:410:5: (c= sident |l= selectionLiteral |f= selectionFunction )
			int alt30=3;
			alt30 = dfa30.predict(input);
			switch (alt30) {
				case 1 :
					// Parser.g:410:7: c= sident
					{
					pushFollow(FOLLOW_sident_in_simpleUnaliasedSelector2300);
					c=sident();
					state._fsp--;
					if (state.failed) return s;
					if ( state.backtracking==0 ) { s = c; }
					}
					break;
				case 2 :
					// Parser.g:411:7: l= selectionLiteral
					{
					pushFollow(FOLLOW_selectionLiteral_in_simpleUnaliasedSelector2346);
					l=selectionLiteral();
					state._fsp--;
					if (state.failed) return s;
					if ( state.backtracking==0 ) { s = new Selectable.WithTerm.Raw(l); }
					}
					break;
				case 3 :
					// Parser.g:412:7: f= selectionFunction
					{
					pushFollow(FOLLOW_selectionFunction_in_simpleUnaliasedSelector2382);
					f=selectionFunction();
					state._fsp--;
					if (state.failed) return s;
					if ( state.backtracking==0 ) { s = f; }
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return s;
	}
	// $ANTLR end "simpleUnaliasedSelector"



	// $ANTLR start "selectionFunction"
	// Parser.g:415:1: selectionFunction returns [Selectable.Raw s] : ( K_COUNT '(' '\\*' ')' | K_WRITETIME '(' c= cident ')' | K_TTL '(' c= cident ')' | K_CAST '(' sn= unaliasedSelector K_AS t= native_type ')' |f= functionName args= selectionFunctionArgs );
	public final Selectable.Raw selectionFunction() throws RecognitionException {
		Selectable.Raw s = null;


		ColumnMetadata.Raw c =null;
		Selectable.Raw sn =null;
		CQL3Type t =null;
		FunctionName f =null;
		List<Selectable.Raw> args =null;

		try {
			// Parser.g:416:5: ( K_COUNT '(' '\\*' ')' | K_WRITETIME '(' c= cident ')' | K_TTL '(' c= cident ')' | K_CAST '(' sn= unaliasedSelector K_AS t= native_type ')' |f= functionName args= selectionFunctionArgs )
			int alt31=5;
			alt31 = dfa31.predict(input);
			switch (alt31) {
				case 1 :
					// Parser.g:416:7: K_COUNT '(' '\\*' ')'
					{
					match(input,K_COUNT,FOLLOW_K_COUNT_in_selectionFunction2428); if (state.failed) return s;
					match(input,190,FOLLOW_190_in_selectionFunction2430); if (state.failed) return s;
					match(input,207,FOLLOW_207_in_selectionFunction2432); if (state.failed) return s;
					match(input,191,FOLLOW_191_in_selectionFunction2434); if (state.failed) return s;
					if ( state.backtracking==0 ) { s = Selectable.WithFunction.Raw.newCountRowsFunction(); }
					}
					break;
				case 2 :
					// Parser.g:417:7: K_WRITETIME '(' c= cident ')'
					{
					match(input,K_WRITETIME,FOLLOW_K_WRITETIME_in_selectionFunction2465); if (state.failed) return s;
					match(input,190,FOLLOW_190_in_selectionFunction2467); if (state.failed) return s;
					pushFollow(FOLLOW_cident_in_selectionFunction2471);
					c=cident();
					state._fsp--;
					if (state.failed) return s;
					match(input,191,FOLLOW_191_in_selectionFunction2473); if (state.failed) return s;
					if ( state.backtracking==0 ) { s = new Selectable.WritetimeOrTTL.Raw(c, true); }
					}
					break;
				case 3 :
					// Parser.g:418:7: K_TTL '(' c= cident ')'
					{
					match(input,K_TTL,FOLLOW_K_TTL_in_selectionFunction2496); if (state.failed) return s;
					match(input,190,FOLLOW_190_in_selectionFunction2504); if (state.failed) return s;
					pushFollow(FOLLOW_cident_in_selectionFunction2508);
					c=cident();
					state._fsp--;
					if (state.failed) return s;
					match(input,191,FOLLOW_191_in_selectionFunction2510); if (state.failed) return s;
					if ( state.backtracking==0 ) { s = new Selectable.WritetimeOrTTL.Raw(c, false); }
					}
					break;
				case 4 :
					// Parser.g:419:7: K_CAST '(' sn= unaliasedSelector K_AS t= native_type ')'
					{
					match(input,K_CAST,FOLLOW_K_CAST_in_selectionFunction2533); if (state.failed) return s;
					match(input,190,FOLLOW_190_in_selectionFunction2540); if (state.failed) return s;
					pushFollow(FOLLOW_unaliasedSelector_in_selectionFunction2544);
					sn=unaliasedSelector();
					state._fsp--;
					if (state.failed) return s;
					match(input,K_AS,FOLLOW_K_AS_in_selectionFunction2546); if (state.failed) return s;
					pushFollow(FOLLOW_native_type_in_selectionFunction2550);
					t=native_type();
					state._fsp--;
					if (state.failed) return s;
					match(input,191,FOLLOW_191_in_selectionFunction2552); if (state.failed) return s;
					if ( state.backtracking==0 ) {s = new Selectable.WithCast.Raw(sn, t);}
					}
					break;
				case 5 :
					// Parser.g:420:7: f= functionName args= selectionFunctionArgs
					{
					pushFollow(FOLLOW_functionName_in_selectionFunction2564);
					f=functionName();
					state._fsp--;
					if (state.failed) return s;
					pushFollow(FOLLOW_selectionFunctionArgs_in_selectionFunction2568);
					args=selectionFunctionArgs();
					state._fsp--;
					if (state.failed) return s;
					if ( state.backtracking==0 ) { s = new Selectable.WithFunction.Raw(f, args); }
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return s;
	}
	// $ANTLR end "selectionFunction"



	// $ANTLR start "selectionLiteral"
	// Parser.g:423:1: selectionLiteral returns [Term.Raw value] : (c= constant | K_NULL | ':' id= noncol_ident | QMARK );
	public final Term.Raw selectionLiteral() throws RecognitionException {
		Term.Raw value = null;


		Constants.Literal c =null;
		ColumnIdentifier id =null;

		try {
			// Parser.g:424:5: (c= constant | K_NULL | ':' id= noncol_ident | QMARK )
			int alt32=4;
			switch ( input.LA(1) ) {
			case BOOLEAN:
			case DURATION:
			case FLOAT:
			case HEXNUMBER:
			case INTEGER:
			case K_NEGATIVE_INFINITY:
			case K_NEGATIVE_NAN:
			case K_POSITIVE_INFINITY:
			case K_POSITIVE_NAN:
			case STRING_LITERAL:
			case UUID:
				{
				alt32=1;
				}
				break;
			case K_NULL:
				{
				alt32=2;
				}
				break;
			case 199:
				{
				alt32=3;
				}
				break;
			case QMARK:
				{
				alt32=4;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return value;}
				NoViableAltException nvae =
					new NoViableAltException("", 32, 0, input);
				throw nvae;
			}
			switch (alt32) {
				case 1 :
					// Parser.g:424:7: c= constant
					{
					pushFollow(FOLLOW_constant_in_selectionLiteral2593);
					c=constant();
					state._fsp--;
					if (state.failed) return value;
					if ( state.backtracking==0 ) { value = c; }
					}
					break;
				case 2 :
					// Parser.g:425:7: K_NULL
					{
					match(input,K_NULL,FOLLOW_K_NULL_in_selectionLiteral2623); if (state.failed) return value;
					if ( state.backtracking==0 ) { value = Constants.NULL_LITERAL; }
					}
					break;
				case 3 :
					// Parser.g:426:7: ':' id= noncol_ident
					{
					match(input,199,FOLLOW_199_in_selectionLiteral2657); if (state.failed) return value;
					pushFollow(FOLLOW_noncol_ident_in_selectionLiteral2661);
					id=noncol_ident();
					state._fsp--;
					if (state.failed) return value;
					if ( state.backtracking==0 ) { value = newBindVariables(id); }
					}
					break;
				case 4 :
					// Parser.g:427:7: QMARK
					{
					match(input,QMARK,FOLLOW_QMARK_in_selectionLiteral2682); if (state.failed) return value;
					if ( state.backtracking==0 ) { value = newBindVariables(null); }
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return value;
	}
	// $ANTLR end "selectionLiteral"



	// $ANTLR start "selectionFunctionArgs"
	// Parser.g:430:1: selectionFunctionArgs returns [List<Selectable.Raw> a] : '(' (s1= unaliasedSelector ( ',' sn= unaliasedSelector )* )? ')' ;
	public final List<Selectable.Raw> selectionFunctionArgs() throws RecognitionException {
		List<Selectable.Raw> a = null;


		Selectable.Raw s1 =null;
		Selectable.Raw sn =null;

		 a = new ArrayList<>(); 
		try {
			// Parser.g:432:5: ( '(' (s1= unaliasedSelector ( ',' sn= unaliasedSelector )* )? ')' )
			// Parser.g:432:7: '(' (s1= unaliasedSelector ( ',' sn= unaliasedSelector )* )? ')'
			{
			match(input,190,FOLLOW_190_in_selectionFunctionArgs2738); if (state.failed) return a;
			// Parser.g:432:11: (s1= unaliasedSelector ( ',' sn= unaliasedSelector )* )?
			int alt34=2;
			int LA34_0 = input.LA(1);
			if ( (LA34_0==BOOLEAN||LA34_0==DURATION||LA34_0==FLOAT||LA34_0==HEXNUMBER||(LA34_0 >= IDENT && LA34_0 <= INTEGER)||(LA34_0 >= K_AGGREGATE && LA34_0 <= K_ALL)||LA34_0==K_AS||LA34_0==K_ASCII||(LA34_0 >= K_BIGINT && LA34_0 <= K_BOOLEAN)||(LA34_0 >= K_CALLED && LA34_0 <= K_CLUSTERING)||(LA34_0 >= K_COMPACT && LA34_0 <= K_COUNTER)||LA34_0==K_CUSTOM||(LA34_0 >= K_DATE && LA34_0 <= K_DECIMAL)||(LA34_0 >= K_DISTINCT && LA34_0 <= K_DOUBLE)||LA34_0==K_DURATION||(LA34_0 >= K_EXISTS && LA34_0 <= K_FLOAT)||LA34_0==K_FROZEN||(LA34_0 >= K_FUNCTION && LA34_0 <= K_FUNCTIONS)||LA34_0==K_GROUP||(LA34_0 >= K_INET && LA34_0 <= K_INPUT)||LA34_0==K_INT||(LA34_0 >= K_JSON && LA34_0 <= K_KEYS)||(LA34_0 >= K_KEYSPACES && LA34_0 <= K_LIKE)||(LA34_0 >= K_LIST && LA34_0 <= K_MAP)||(LA34_0 >= K_NEGATIVE_INFINITY && LA34_0 <= K_NOLOGIN)||LA34_0==K_NOSUPERUSER||LA34_0==K_NULL||LA34_0==K_OPTIONS||(LA34_0 >= K_PARTITION && LA34_0 <= K_POSITIVE_NAN)||LA34_0==K_RETURNS||(LA34_0 >= K_ROLE && LA34_0 <= K_ROLES)||(LA34_0 >= K_SFUNC && LA34_0 <= K_TINYINT)||(LA34_0 >= K_TOKEN && LA34_0 <= K_TRIGGER)||(LA34_0 >= K_TTL && LA34_0 <= K_TYPE)||(LA34_0 >= K_USER && LA34_0 <= K_USERS)||(LA34_0 >= K_UUID && LA34_0 <= K_VARINT)||LA34_0==K_WRITETIME||(LA34_0 >= QMARK && LA34_0 <= QUOTED_NAME)||LA34_0==STRING_LITERAL||LA34_0==UUID||LA34_0==190||LA34_0==195||LA34_0==199||LA34_0==206||LA34_0==210) ) {
				alt34=1;
			}
			switch (alt34) {
				case 1 :
					// Parser.g:432:12: s1= unaliasedSelector ( ',' sn= unaliasedSelector )*
					{
					pushFollow(FOLLOW_unaliasedSelector_in_selectionFunctionArgs2743);
					s1=unaliasedSelector();
					state._fsp--;
					if (state.failed) return a;
					if ( state.backtracking==0 ) { a.add(s1); }
					// Parser.g:433:11: ( ',' sn= unaliasedSelector )*
					loop33:
					while (true) {
						int alt33=2;
						int LA33_0 = input.LA(1);
						if ( (LA33_0==194) ) {
							alt33=1;
						}

						switch (alt33) {
						case 1 :
							// Parser.g:433:13: ',' sn= unaliasedSelector
							{
							match(input,194,FOLLOW_194_in_selectionFunctionArgs2759); if (state.failed) return a;
							pushFollow(FOLLOW_unaliasedSelector_in_selectionFunctionArgs2763);
							sn=unaliasedSelector();
							state._fsp--;
							if (state.failed) return a;
							if ( state.backtracking==0 ) { a.add(sn); }
							}
							break;

						default :
							break loop33;
						}
					}

					}
					break;

			}

			match(input,191,FOLLOW_191_in_selectionFunctionArgs2778); if (state.failed) return a;
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return a;
	}
	// $ANTLR end "selectionFunctionArgs"



	// $ANTLR start "sident"
	// Parser.g:437:1: sident returns [Selectable.Raw id] : (t= IDENT |t= QUOTED_NAME |k= unreserved_keyword );
	public final Selectable.Raw sident() throws RecognitionException {
		Selectable.Raw id = null;


		Token t=null;
		String k =null;

		try {
			// Parser.g:438:5: (t= IDENT |t= QUOTED_NAME |k= unreserved_keyword )
			int alt35=3;
			switch ( input.LA(1) ) {
			case IDENT:
				{
				alt35=1;
				}
				break;
			case QUOTED_NAME:
				{
				alt35=2;
				}
				break;
			case K_AGGREGATE:
			case K_ALL:
			case K_AS:
			case K_ASCII:
			case K_BIGINT:
			case K_BLOB:
			case K_BOOLEAN:
			case K_CALLED:
			case K_CAST:
			case K_CLUSTERING:
			case K_COMPACT:
			case K_CONTAINS:
			case K_COUNT:
			case K_COUNTER:
			case K_CUSTOM:
			case K_DATE:
			case K_DECIMAL:
			case K_DISTINCT:
			case K_DOUBLE:
			case K_DURATION:
			case K_EXISTS:
			case K_FILTERING:
			case K_FINALFUNC:
			case K_FLOAT:
			case K_FROZEN:
			case K_FUNCTION:
			case K_FUNCTIONS:
			case K_GROUP:
			case K_INET:
			case K_INITCOND:
			case K_INPUT:
			case K_INT:
			case K_JSON:
			case K_KEY:
			case K_KEYS:
			case K_KEYSPACES:
			case K_LANGUAGE:
			case K_LIKE:
			case K_LIST:
			case K_LOGIN:
			case K_MAP:
			case K_NOLOGIN:
			case K_NOSUPERUSER:
			case K_OPTIONS:
			case K_PARTITION:
			case K_PASSWORD:
			case K_PER:
			case K_PERMISSION:
			case K_PERMISSIONS:
			case K_RETURNS:
			case K_ROLE:
			case K_ROLES:
			case K_SFUNC:
			case K_SMALLINT:
			case K_STATIC:
			case K_STORAGE:
			case K_STYPE:
			case K_SUPERUSER:
			case K_TEXT:
			case K_TIME:
			case K_TIMESTAMP:
			case K_TIMEUUID:
			case K_TINYINT:
			case K_TRIGGER:
			case K_TTL:
			case K_TUPLE:
			case K_TYPE:
			case K_USER:
			case K_USERS:
			case K_UUID:
			case K_VALUES:
			case K_VARCHAR:
			case K_VARINT:
			case K_WRITETIME:
				{
				alt35=3;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return id;}
				NoViableAltException nvae =
					new NoViableAltException("", 35, 0, input);
				throw nvae;
			}
			switch (alt35) {
				case 1 :
					// Parser.g:438:7: t= IDENT
					{
					t=(Token)match(input,IDENT,FOLLOW_IDENT_in_sident2801); if (state.failed) return id;
					if ( state.backtracking==0 ) { id = Selectable.RawIdentifier.forUnquoted((t!=null?t.getText():null)); }
					}
					break;
				case 2 :
					// Parser.g:439:7: t= QUOTED_NAME
					{
					t=(Token)match(input,QUOTED_NAME,FOLLOW_QUOTED_NAME_in_sident2826); if (state.failed) return id;
					if ( state.backtracking==0 ) { id = Selectable.RawIdentifier.forQuoted((t!=null?t.getText():null)); }
					}
					break;
				case 3 :
					// Parser.g:440:7: k= unreserved_keyword
					{
					pushFollow(FOLLOW_unreserved_keyword_in_sident2845);
					k=unreserved_keyword();
					state._fsp--;
					if (state.failed) return id;
					if ( state.backtracking==0 ) { id = Selectable.RawIdentifier.forUnquoted(k); }
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return id;
	}
	// $ANTLR end "sident"



	// $ANTLR start "whereClause"
	// Parser.g:443:1: whereClause returns [WhereClause.Builder clause] : relationOrExpression[$clause] ( K_AND relationOrExpression[$clause] )* ;
	public final WhereClause.Builder whereClause() throws RecognitionException {
		WhereClause.Builder clause = null;


		 clause = new WhereClause.Builder(); 
		try {
			// Parser.g:445:5: ( relationOrExpression[$clause] ( K_AND relationOrExpression[$clause] )* )
			// Parser.g:445:7: relationOrExpression[$clause] ( K_AND relationOrExpression[$clause] )*
			{
			pushFollow(FOLLOW_relationOrExpression_in_whereClause2876);
			relationOrExpression(clause);
			state._fsp--;
			if (state.failed) return clause;
			// Parser.g:445:37: ( K_AND relationOrExpression[$clause] )*
			loop36:
			while (true) {
				int alt36=2;
				int LA36_0 = input.LA(1);
				if ( (LA36_0==K_AND) ) {
					alt36=1;
				}

				switch (alt36) {
				case 1 :
					// Parser.g:445:38: K_AND relationOrExpression[$clause]
					{
					match(input,K_AND,FOLLOW_K_AND_in_whereClause2880); if (state.failed) return clause;
					pushFollow(FOLLOW_relationOrExpression_in_whereClause2882);
					relationOrExpression(clause);
					state._fsp--;
					if (state.failed) return clause;
					}
					break;

				default :
					break loop36;
				}
			}

			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return clause;
	}
	// $ANTLR end "whereClause"



	// $ANTLR start "relationOrExpression"
	// Parser.g:448:1: relationOrExpression[WhereClause.Builder clause] : ( relation[$clause] | customIndexExpression[$clause] );
	public final void relationOrExpression(WhereClause.Builder clause) throws RecognitionException {
		try {
			// Parser.g:449:5: ( relation[$clause] | customIndexExpression[$clause] )
			int alt37=2;
			int LA37_0 = input.LA(1);
			if ( (LA37_0==EMPTY_QUOTED_NAME||LA37_0==IDENT||(LA37_0 >= K_AGGREGATE && LA37_0 <= K_ALL)||LA37_0==K_AS||LA37_0==K_ASCII||(LA37_0 >= K_BIGINT && LA37_0 <= K_BOOLEAN)||(LA37_0 >= K_CALLED && LA37_0 <= K_CLUSTERING)||(LA37_0 >= K_COMPACT && LA37_0 <= K_COUNTER)||LA37_0==K_CUSTOM||(LA37_0 >= K_DATE && LA37_0 <= K_DECIMAL)||(LA37_0 >= K_DISTINCT && LA37_0 <= K_DOUBLE)||LA37_0==K_DURATION||(LA37_0 >= K_EXISTS && LA37_0 <= K_FLOAT)||LA37_0==K_FROZEN||(LA37_0 >= K_FUNCTION && LA37_0 <= K_FUNCTIONS)||LA37_0==K_GROUP||(LA37_0 >= K_INET && LA37_0 <= K_INPUT)||LA37_0==K_INT||(LA37_0 >= K_JSON && LA37_0 <= K_KEYS)||(LA37_0 >= K_KEYSPACES && LA37_0 <= K_LIKE)||(LA37_0 >= K_LIST && LA37_0 <= K_MAP)||LA37_0==K_NOLOGIN||LA37_0==K_NOSUPERUSER||LA37_0==K_OPTIONS||(LA37_0 >= K_PARTITION && LA37_0 <= K_PERMISSIONS)||LA37_0==K_RETURNS||(LA37_0 >= K_ROLE && LA37_0 <= K_ROLES)||(LA37_0 >= K_SFUNC && LA37_0 <= K_TINYINT)||(LA37_0 >= K_TOKEN && LA37_0 <= K_TRIGGER)||(LA37_0 >= K_TTL && LA37_0 <= K_TYPE)||(LA37_0 >= K_USER && LA37_0 <= K_USERS)||(LA37_0 >= K_UUID && LA37_0 <= K_VARINT)||LA37_0==K_WRITETIME||LA37_0==QUOTED_NAME||LA37_0==190) ) {
				alt37=1;
			}
			else if ( (LA37_0==209) ) {
				alt37=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return;}
				NoViableAltException nvae =
					new NoViableAltException("", 37, 0, input);
				throw nvae;
			}

			switch (alt37) {
				case 1 :
					// Parser.g:449:7: relation[$clause]
					{
					pushFollow(FOLLOW_relation_in_relationOrExpression2904);
					relation(clause);
					state._fsp--;
					if (state.failed) return;
					}
					break;
				case 2 :
					// Parser.g:450:7: customIndexExpression[$clause]
					{
					pushFollow(FOLLOW_customIndexExpression_in_relationOrExpression2913);
					customIndexExpression(clause);
					state._fsp--;
					if (state.failed) return;
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "relationOrExpression"



	// $ANTLR start "customIndexExpression"
	// Parser.g:453:1: customIndexExpression[WhereClause.Builder clause] : 'expr(' idxName[name] ',' t= term ')' ;
	public final void customIndexExpression(WhereClause.Builder clause) throws RecognitionException {
		Term.Raw t =null;

		QualifiedName name = new QualifiedName();
		try {
			// Parser.g:455:5: ( 'expr(' idxName[name] ',' t= term ')' )
			// Parser.g:455:7: 'expr(' idxName[name] ',' t= term ')'
			{
			match(input,209,FOLLOW_209_in_customIndexExpression2941); if (state.failed) return;
			pushFollow(FOLLOW_idxName_in_customIndexExpression2943);
			idxName(name);
			state._fsp--;
			if (state.failed) return;
			match(input,194,FOLLOW_194_in_customIndexExpression2946); if (state.failed) return;
			pushFollow(FOLLOW_term_in_customIndexExpression2950);
			t=term();
			state._fsp--;
			if (state.failed) return;
			match(input,191,FOLLOW_191_in_customIndexExpression2952); if (state.failed) return;
			if ( state.backtracking==0 ) { clause.add(new CustomIndexExpression(name, t));}
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "customIndexExpression"



	// $ANTLR start "orderByClause"
	// Parser.g:458:1: orderByClause[Map<ColumnMetadata.Raw, Boolean> orderings] : c= cident ( K_ASC | K_DESC )? ;
	public final void orderByClause(Map<ColumnMetadata.Raw, Boolean> orderings) throws RecognitionException {
		ColumnMetadata.Raw c =null;


		        boolean reversed = false;
		    
		try {
			// Parser.g:462:5: (c= cident ( K_ASC | K_DESC )? )
			// Parser.g:462:7: c= cident ( K_ASC | K_DESC )?
			{
			pushFollow(FOLLOW_cident_in_orderByClause2982);
			c=cident();
			state._fsp--;
			if (state.failed) return;
			// Parser.g:462:16: ( K_ASC | K_DESC )?
			int alt38=3;
			int LA38_0 = input.LA(1);
			if ( (LA38_0==K_ASC) ) {
				alt38=1;
			}
			else if ( (LA38_0==K_DESC) ) {
				alt38=2;
			}
			switch (alt38) {
				case 1 :
					// Parser.g:462:17: K_ASC
					{
					match(input,K_ASC,FOLLOW_K_ASC_in_orderByClause2985); if (state.failed) return;
					}
					break;
				case 2 :
					// Parser.g:462:25: K_DESC
					{
					match(input,K_DESC,FOLLOW_K_DESC_in_orderByClause2989); if (state.failed) return;
					if ( state.backtracking==0 ) { reversed = true; }
					}
					break;

			}

			if ( state.backtracking==0 ) { orderings.put(c, reversed); }
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "orderByClause"



	// $ANTLR start "groupByClause"
	// Parser.g:465:1: groupByClause[List<ColumnMetadata.Raw> groups] : c= cident ;
	public final void groupByClause(List<ColumnMetadata.Raw> groups) throws RecognitionException {
		ColumnMetadata.Raw c =null;

		try {
			// Parser.g:466:5: (c= cident )
			// Parser.g:466:7: c= cident
			{
			pushFollow(FOLLOW_cident_in_groupByClause3015);
			c=cident();
			state._fsp--;
			if (state.failed) return;
			if ( state.backtracking==0 ) { groups.add(c); }
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "groupByClause"



	// $ANTLR start "insertStatement"
	// Parser.g:475:1: insertStatement returns [ModificationStatement.Parsed expr] : K_INSERT K_INTO cf= columnFamilyName (st1= normalInsertStatement[cf] | K_JSON st2= jsonInsertStatement[cf] ) ;
	public final ModificationStatement.Parsed insertStatement() throws RecognitionException {
		ModificationStatement.Parsed expr = null;


		QualifiedName cf =null;
		UpdateStatement.ParsedInsert st1 =null;
		UpdateStatement.ParsedInsertJson st2 =null;

		try {
			// Parser.g:476:5: ( K_INSERT K_INTO cf= columnFamilyName (st1= normalInsertStatement[cf] | K_JSON st2= jsonInsertStatement[cf] ) )
			// Parser.g:476:7: K_INSERT K_INTO cf= columnFamilyName (st1= normalInsertStatement[cf] | K_JSON st2= jsonInsertStatement[cf] )
			{
			match(input,K_INSERT,FOLLOW_K_INSERT_in_insertStatement3040); if (state.failed) return expr;
			match(input,K_INTO,FOLLOW_K_INTO_in_insertStatement3042); if (state.failed) return expr;
			pushFollow(FOLLOW_columnFamilyName_in_insertStatement3046);
			cf=columnFamilyName();
			state._fsp--;
			if (state.failed) return expr;
			// Parser.g:477:9: (st1= normalInsertStatement[cf] | K_JSON st2= jsonInsertStatement[cf] )
			int alt39=2;
			int LA39_0 = input.LA(1);
			if ( (LA39_0==190) ) {
				alt39=1;
			}
			else if ( (LA39_0==K_JSON) ) {
				alt39=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return expr;}
				NoViableAltException nvae =
					new NoViableAltException("", 39, 0, input);
				throw nvae;
			}

			switch (alt39) {
				case 1 :
					// Parser.g:477:11: st1= normalInsertStatement[cf]
					{
					pushFollow(FOLLOW_normalInsertStatement_in_insertStatement3060);
					st1=normalInsertStatement(cf);
					state._fsp--;
					if (state.failed) return expr;
					if ( state.backtracking==0 ) { expr = st1; }
					}
					break;
				case 2 :
					// Parser.g:478:11: K_JSON st2= jsonInsertStatement[cf]
					{
					match(input,K_JSON,FOLLOW_K_JSON_in_insertStatement3075); if (state.failed) return expr;
					pushFollow(FOLLOW_jsonInsertStatement_in_insertStatement3079);
					st2=jsonInsertStatement(cf);
					state._fsp--;
					if (state.failed) return expr;
					if ( state.backtracking==0 ) { expr = st2; }
					}
					break;

			}

			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return expr;
	}
	// $ANTLR end "insertStatement"



	// $ANTLR start "normalInsertStatement"
	// Parser.g:481:1: normalInsertStatement[QualifiedName qn] returns [UpdateStatement.ParsedInsert expr] : '(' c1= cident ( ',' cn= cident )* ')' K_VALUES '(' v1= term ( ',' vn= term )* ')' ( K_IF K_NOT K_EXISTS )? ( usingClause[attrs] )? ;
	public final UpdateStatement.ParsedInsert normalInsertStatement(QualifiedName qn) throws RecognitionException {
		UpdateStatement.ParsedInsert expr = null;


		ColumnMetadata.Raw c1 =null;
		ColumnMetadata.Raw cn =null;
		Term.Raw v1 =null;
		Term.Raw vn =null;


		        Attributes.Raw attrs = new Attributes.Raw();
		        List<ColumnMetadata.Raw> columnNames  = new ArrayList<>();
		        List<Term.Raw> values = new ArrayList<>();
		        boolean ifNotExists = false;
		    
		try {
			// Parser.g:488:5: ( '(' c1= cident ( ',' cn= cident )* ')' K_VALUES '(' v1= term ( ',' vn= term )* ')' ( K_IF K_NOT K_EXISTS )? ( usingClause[attrs] )? )
			// Parser.g:488:7: '(' c1= cident ( ',' cn= cident )* ')' K_VALUES '(' v1= term ( ',' vn= term )* ')' ( K_IF K_NOT K_EXISTS )? ( usingClause[attrs] )?
			{
			match(input,190,FOLLOW_190_in_normalInsertStatement3115); if (state.failed) return expr;
			pushFollow(FOLLOW_cident_in_normalInsertStatement3119);
			c1=cident();
			state._fsp--;
			if (state.failed) return expr;
			if ( state.backtracking==0 ) { columnNames.add(c1); }
			// Parser.g:488:47: ( ',' cn= cident )*
			loop40:
			while (true) {
				int alt40=2;
				int LA40_0 = input.LA(1);
				if ( (LA40_0==194) ) {
					alt40=1;
				}

				switch (alt40) {
				case 1 :
					// Parser.g:488:49: ',' cn= cident
					{
					match(input,194,FOLLOW_194_in_normalInsertStatement3126); if (state.failed) return expr;
					pushFollow(FOLLOW_cident_in_normalInsertStatement3130);
					cn=cident();
					state._fsp--;
					if (state.failed) return expr;
					if ( state.backtracking==0 ) { columnNames.add(cn); }
					}
					break;

				default :
					break loop40;
				}
			}

			match(input,191,FOLLOW_191_in_normalInsertStatement3137); if (state.failed) return expr;
			match(input,K_VALUES,FOLLOW_K_VALUES_in_normalInsertStatement3145); if (state.failed) return expr;
			match(input,190,FOLLOW_190_in_normalInsertStatement3153); if (state.failed) return expr;
			pushFollow(FOLLOW_term_in_normalInsertStatement3157);
			v1=term();
			state._fsp--;
			if (state.failed) return expr;
			if ( state.backtracking==0 ) { values.add(v1); }
			// Parser.g:490:39: ( ',' vn= term )*
			loop41:
			while (true) {
				int alt41=2;
				int LA41_0 = input.LA(1);
				if ( (LA41_0==194) ) {
					alt41=1;
				}

				switch (alt41) {
				case 1 :
					// Parser.g:490:41: ',' vn= term
					{
					match(input,194,FOLLOW_194_in_normalInsertStatement3163); if (state.failed) return expr;
					pushFollow(FOLLOW_term_in_normalInsertStatement3167);
					vn=term();
					state._fsp--;
					if (state.failed) return expr;
					if ( state.backtracking==0 ) { values.add(vn); }
					}
					break;

				default :
					break loop41;
				}
			}

			match(input,191,FOLLOW_191_in_normalInsertStatement3174); if (state.failed) return expr;
			// Parser.g:491:7: ( K_IF K_NOT K_EXISTS )?
			int alt42=2;
			int LA42_0 = input.LA(1);
			if ( (LA42_0==K_IF) ) {
				alt42=1;
			}
			switch (alt42) {
				case 1 :
					// Parser.g:491:9: K_IF K_NOT K_EXISTS
					{
					match(input,K_IF,FOLLOW_K_IF_in_normalInsertStatement3184); if (state.failed) return expr;
					match(input,K_NOT,FOLLOW_K_NOT_in_normalInsertStatement3186); if (state.failed) return expr;
					match(input,K_EXISTS,FOLLOW_K_EXISTS_in_normalInsertStatement3188); if (state.failed) return expr;
					if ( state.backtracking==0 ) { ifNotExists = true; }
					}
					break;

			}

			// Parser.g:492:7: ( usingClause[attrs] )?
			int alt43=2;
			int LA43_0 = input.LA(1);
			if ( (LA43_0==K_USING) ) {
				alt43=1;
			}
			switch (alt43) {
				case 1 :
					// Parser.g:492:9: usingClause[attrs]
					{
					pushFollow(FOLLOW_usingClause_in_normalInsertStatement3203);
					usingClause(attrs);
					state._fsp--;
					if (state.failed) return expr;
					}
					break;

			}

			if ( state.backtracking==0 ) {
			          expr = new UpdateStatement.ParsedInsert(qn, attrs, columnNames, values, ifNotExists);
			      }
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return expr;
	}
	// $ANTLR end "normalInsertStatement"



	// $ANTLR start "jsonInsertStatement"
	// Parser.g:498:1: jsonInsertStatement[QualifiedName qn] returns [UpdateStatement.ParsedInsertJson expr] : val= jsonValue ( K_DEFAULT ( K_NULL | ( K_UNSET ) ) )? ( K_IF K_NOT K_EXISTS )? ( usingClause[attrs] )? ;
	public final UpdateStatement.ParsedInsertJson jsonInsertStatement(QualifiedName qn) throws RecognitionException {
		UpdateStatement.ParsedInsertJson expr = null;


		Json.Raw val =null;


		        Attributes.Raw attrs = new Attributes.Raw();
		        boolean ifNotExists = false;
		        boolean defaultUnset = false;
		    
		try {
			// Parser.g:504:5: (val= jsonValue ( K_DEFAULT ( K_NULL | ( K_UNSET ) ) )? ( K_IF K_NOT K_EXISTS )? ( usingClause[attrs] )? )
			// Parser.g:504:7: val= jsonValue ( K_DEFAULT ( K_NULL | ( K_UNSET ) ) )? ( K_IF K_NOT K_EXISTS )? ( usingClause[attrs] )?
			{
			pushFollow(FOLLOW_jsonValue_in_jsonInsertStatement3249);
			val=jsonValue();
			state._fsp--;
			if (state.failed) return expr;
			// Parser.g:505:7: ( K_DEFAULT ( K_NULL | ( K_UNSET ) ) )?
			int alt45=2;
			int LA45_0 = input.LA(1);
			if ( (LA45_0==K_DEFAULT) ) {
				alt45=1;
			}
			switch (alt45) {
				case 1 :
					// Parser.g:505:9: K_DEFAULT ( K_NULL | ( K_UNSET ) )
					{
					match(input,K_DEFAULT,FOLLOW_K_DEFAULT_in_jsonInsertStatement3259); if (state.failed) return expr;
					// Parser.g:505:19: ( K_NULL | ( K_UNSET ) )
					int alt44=2;
					int LA44_0 = input.LA(1);
					if ( (LA44_0==K_NULL) ) {
						alt44=1;
					}
					else if ( (LA44_0==K_UNSET) ) {
						alt44=2;
					}

					else {
						if (state.backtracking>0) {state.failed=true; return expr;}
						NoViableAltException nvae =
							new NoViableAltException("", 44, 0, input);
						throw nvae;
					}

					switch (alt44) {
						case 1 :
							// Parser.g:505:21: K_NULL
							{
							match(input,K_NULL,FOLLOW_K_NULL_in_jsonInsertStatement3263); if (state.failed) return expr;
							}
							break;
						case 2 :
							// Parser.g:505:30: ( K_UNSET )
							{
							// Parser.g:505:30: ( K_UNSET )
							// Parser.g:505:32: K_UNSET
							{
							if ( state.backtracking==0 ) { defaultUnset = true; }
							match(input,K_UNSET,FOLLOW_K_UNSET_in_jsonInsertStatement3271); if (state.failed) return expr;
							}

							}
							break;

					}

					}
					break;

			}

			// Parser.g:506:7: ( K_IF K_NOT K_EXISTS )?
			int alt46=2;
			int LA46_0 = input.LA(1);
			if ( (LA46_0==K_IF) ) {
				alt46=1;
			}
			switch (alt46) {
				case 1 :
					// Parser.g:506:9: K_IF K_NOT K_EXISTS
					{
					match(input,K_IF,FOLLOW_K_IF_in_jsonInsertStatement3287); if (state.failed) return expr;
					match(input,K_NOT,FOLLOW_K_NOT_in_jsonInsertStatement3289); if (state.failed) return expr;
					match(input,K_EXISTS,FOLLOW_K_EXISTS_in_jsonInsertStatement3291); if (state.failed) return expr;
					if ( state.backtracking==0 ) { ifNotExists = true; }
					}
					break;

			}

			// Parser.g:507:7: ( usingClause[attrs] )?
			int alt47=2;
			int LA47_0 = input.LA(1);
			if ( (LA47_0==K_USING) ) {
				alt47=1;
			}
			switch (alt47) {
				case 1 :
					// Parser.g:507:9: usingClause[attrs]
					{
					pushFollow(FOLLOW_usingClause_in_jsonInsertStatement3306);
					usingClause(attrs);
					state._fsp--;
					if (state.failed) return expr;
					}
					break;

			}

			if ( state.backtracking==0 ) {
			          expr = new UpdateStatement.ParsedInsertJson(qn, attrs, val, defaultUnset, ifNotExists);
			      }
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return expr;
	}
	// $ANTLR end "jsonInsertStatement"



	// $ANTLR start "jsonValue"
	// Parser.g:513:1: jsonValue returns [Json.Raw value] : (s= STRING_LITERAL | ':' id= noncol_ident | QMARK );
	public final Json.Raw jsonValue() throws RecognitionException {
		Json.Raw value = null;


		Token s=null;
		ColumnIdentifier id =null;

		try {
			// Parser.g:514:5: (s= STRING_LITERAL | ':' id= noncol_ident | QMARK )
			int alt48=3;
			switch ( input.LA(1) ) {
			case STRING_LITERAL:
				{
				alt48=1;
				}
				break;
			case 199:
				{
				alt48=2;
				}
				break;
			case QMARK:
				{
				alt48=3;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return value;}
				NoViableAltException nvae =
					new NoViableAltException("", 48, 0, input);
				throw nvae;
			}
			switch (alt48) {
				case 1 :
					// Parser.g:514:7: s= STRING_LITERAL
					{
					s=(Token)match(input,STRING_LITERAL,FOLLOW_STRING_LITERAL_in_jsonValue3341); if (state.failed) return value;
					if ( state.backtracking==0 ) { value = new Json.Literal((s!=null?s.getText():null)); }
					}
					break;
				case 2 :
					// Parser.g:515:7: ':' id= noncol_ident
					{
					match(input,199,FOLLOW_199_in_jsonValue3351); if (state.failed) return value;
					pushFollow(FOLLOW_noncol_ident_in_jsonValue3355);
					id=noncol_ident();
					state._fsp--;
					if (state.failed) return value;
					if ( state.backtracking==0 ) { value = newJsonBindVariables(id); }
					}
					break;
				case 3 :
					// Parser.g:516:7: QMARK
					{
					match(input,QMARK,FOLLOW_QMARK_in_jsonValue3369); if (state.failed) return value;
					if ( state.backtracking==0 ) { value = newJsonBindVariables(null); }
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return value;
	}
	// $ANTLR end "jsonValue"



	// $ANTLR start "usingClause"
	// Parser.g:519:1: usingClause[Attributes.Raw attrs] : K_USING usingClauseObjective[attrs] ( K_AND usingClauseObjective[attrs] )* ;
	public final void usingClause(Attributes.Raw attrs) throws RecognitionException {
		try {
			// Parser.g:520:5: ( K_USING usingClauseObjective[attrs] ( K_AND usingClauseObjective[attrs] )* )
			// Parser.g:520:7: K_USING usingClauseObjective[attrs] ( K_AND usingClauseObjective[attrs] )*
			{
			match(input,K_USING,FOLLOW_K_USING_in_usingClause3400); if (state.failed) return;
			pushFollow(FOLLOW_usingClauseObjective_in_usingClause3402);
			usingClauseObjective(attrs);
			state._fsp--;
			if (state.failed) return;
			// Parser.g:520:43: ( K_AND usingClauseObjective[attrs] )*
			loop49:
			while (true) {
				int alt49=2;
				int LA49_0 = input.LA(1);
				if ( (LA49_0==K_AND) ) {
					alt49=1;
				}

				switch (alt49) {
				case 1 :
					// Parser.g:520:45: K_AND usingClauseObjective[attrs]
					{
					match(input,K_AND,FOLLOW_K_AND_in_usingClause3407); if (state.failed) return;
					pushFollow(FOLLOW_usingClauseObjective_in_usingClause3409);
					usingClauseObjective(attrs);
					state._fsp--;
					if (state.failed) return;
					}
					break;

				default :
					break loop49;
				}
			}

			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "usingClause"



	// $ANTLR start "usingClauseObjective"
	// Parser.g:523:1: usingClauseObjective[Attributes.Raw attrs] : ( K_TIMESTAMP ts= intValue | K_TTL t= intValue );
	public final void usingClauseObjective(Attributes.Raw attrs) throws RecognitionException {
		Term.Raw ts =null;
		Term.Raw t =null;

		try {
			// Parser.g:524:5: ( K_TIMESTAMP ts= intValue | K_TTL t= intValue )
			int alt50=2;
			int LA50_0 = input.LA(1);
			if ( (LA50_0==K_TIMESTAMP) ) {
				alt50=1;
			}
			else if ( (LA50_0==K_TTL) ) {
				alt50=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return;}
				NoViableAltException nvae =
					new NoViableAltException("", 50, 0, input);
				throw nvae;
			}

			switch (alt50) {
				case 1 :
					// Parser.g:524:7: K_TIMESTAMP ts= intValue
					{
					match(input,K_TIMESTAMP,FOLLOW_K_TIMESTAMP_in_usingClauseObjective3431); if (state.failed) return;
					pushFollow(FOLLOW_intValue_in_usingClauseObjective3435);
					ts=intValue();
					state._fsp--;
					if (state.failed) return;
					if ( state.backtracking==0 ) { attrs.timestamp = ts; }
					}
					break;
				case 2 :
					// Parser.g:525:7: K_TTL t= intValue
					{
					match(input,K_TTL,FOLLOW_K_TTL_in_usingClauseObjective3445); if (state.failed) return;
					pushFollow(FOLLOW_intValue_in_usingClauseObjective3449);
					t=intValue();
					state._fsp--;
					if (state.failed) return;
					if ( state.backtracking==0 ) { attrs.timeToLive = t; }
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "usingClauseObjective"



	// $ANTLR start "updateStatement"
	// Parser.g:535:1: updateStatement returns [UpdateStatement.ParsedUpdate expr] : K_UPDATE cf= columnFamilyName ( usingClause[attrs] )? K_SET columnOperation[operations] ( ',' columnOperation[operations] )* K_WHERE wclause= whereClause ( K_IF ( K_EXISTS |conditions= updateConditions ) )? ;
	public final UpdateStatement.ParsedUpdate updateStatement() throws RecognitionException {
		UpdateStatement.ParsedUpdate expr = null;


		QualifiedName cf =null;
		WhereClause.Builder wclause =null;
		List<Pair<ColumnMetadata.Raw, ColumnCondition.Raw>> conditions =null;


		        Attributes.Raw attrs = new Attributes.Raw();
		        List<Pair<ColumnMetadata.Raw, Operation.RawUpdate>> operations = new ArrayList<>();
		        boolean ifExists = false;
		    
		try {
			// Parser.g:541:5: ( K_UPDATE cf= columnFamilyName ( usingClause[attrs] )? K_SET columnOperation[operations] ( ',' columnOperation[operations] )* K_WHERE wclause= whereClause ( K_IF ( K_EXISTS |conditions= updateConditions ) )? )
			// Parser.g:541:7: K_UPDATE cf= columnFamilyName ( usingClause[attrs] )? K_SET columnOperation[operations] ( ',' columnOperation[operations] )* K_WHERE wclause= whereClause ( K_IF ( K_EXISTS |conditions= updateConditions ) )?
			{
			match(input,K_UPDATE,FOLLOW_K_UPDATE_in_updateStatement3483); if (state.failed) return expr;
			pushFollow(FOLLOW_columnFamilyName_in_updateStatement3487);
			cf=columnFamilyName();
			state._fsp--;
			if (state.failed) return expr;
			// Parser.g:542:7: ( usingClause[attrs] )?
			int alt51=2;
			int LA51_0 = input.LA(1);
			if ( (LA51_0==K_USING) ) {
				alt51=1;
			}
			switch (alt51) {
				case 1 :
					// Parser.g:542:9: usingClause[attrs]
					{
					pushFollow(FOLLOW_usingClause_in_updateStatement3497);
					usingClause(attrs);
					state._fsp--;
					if (state.failed) return expr;
					}
					break;

			}

			match(input,K_SET,FOLLOW_K_SET_in_updateStatement3509); if (state.failed) return expr;
			pushFollow(FOLLOW_columnOperation_in_updateStatement3511);
			columnOperation(operations);
			state._fsp--;
			if (state.failed) return expr;
			// Parser.g:543:41: ( ',' columnOperation[operations] )*
			loop52:
			while (true) {
				int alt52=2;
				int LA52_0 = input.LA(1);
				if ( (LA52_0==194) ) {
					alt52=1;
				}

				switch (alt52) {
				case 1 :
					// Parser.g:543:42: ',' columnOperation[operations]
					{
					match(input,194,FOLLOW_194_in_updateStatement3515); if (state.failed) return expr;
					pushFollow(FOLLOW_columnOperation_in_updateStatement3517);
					columnOperation(operations);
					state._fsp--;
					if (state.failed) return expr;
					}
					break;

				default :
					break loop52;
				}
			}

			match(input,K_WHERE,FOLLOW_K_WHERE_in_updateStatement3528); if (state.failed) return expr;
			pushFollow(FOLLOW_whereClause_in_updateStatement3532);
			wclause=whereClause();
			state._fsp--;
			if (state.failed) return expr;
			// Parser.g:545:7: ( K_IF ( K_EXISTS |conditions= updateConditions ) )?
			int alt54=2;
			int LA54_0 = input.LA(1);
			if ( (LA54_0==K_IF) ) {
				alt54=1;
			}
			switch (alt54) {
				case 1 :
					// Parser.g:545:9: K_IF ( K_EXISTS |conditions= updateConditions )
					{
					match(input,K_IF,FOLLOW_K_IF_in_updateStatement3542); if (state.failed) return expr;
					// Parser.g:545:14: ( K_EXISTS |conditions= updateConditions )
					int alt53=2;
					int LA53_0 = input.LA(1);
					if ( (LA53_0==K_EXISTS) ) {
						int LA53_1 = input.LA(2);
						if ( (LA53_1==EOF||LA53_1==K_APPLY||LA53_1==K_DELETE||LA53_1==K_INSERT||LA53_1==K_UPDATE||LA53_1==200) ) {
							alt53=1;
						}
						else if ( (LA53_1==K_IN||LA53_1==188||LA53_1==197||(LA53_1 >= 201 && LA53_1 <= 206)) ) {
							alt53=2;
						}

						else {
							if (state.backtracking>0) {state.failed=true; return expr;}
							int nvaeMark = input.mark();
							try {
								input.consume();
								NoViableAltException nvae =
									new NoViableAltException("", 53, 1, input);
								throw nvae;
							} finally {
								input.rewind(nvaeMark);
							}
						}

					}
					else if ( (LA53_0==EMPTY_QUOTED_NAME||LA53_0==IDENT||(LA53_0 >= K_AGGREGATE && LA53_0 <= K_ALL)||LA53_0==K_AS||LA53_0==K_ASCII||(LA53_0 >= K_BIGINT && LA53_0 <= K_BOOLEAN)||(LA53_0 >= K_CALLED && LA53_0 <= K_CLUSTERING)||(LA53_0 >= K_COMPACT && LA53_0 <= K_COUNTER)||LA53_0==K_CUSTOM||(LA53_0 >= K_DATE && LA53_0 <= K_DECIMAL)||(LA53_0 >= K_DISTINCT && LA53_0 <= K_DOUBLE)||LA53_0==K_DURATION||(LA53_0 >= K_FILTERING && LA53_0 <= K_FLOAT)||LA53_0==K_FROZEN||(LA53_0 >= K_FUNCTION && LA53_0 <= K_FUNCTIONS)||LA53_0==K_GROUP||(LA53_0 >= K_INET && LA53_0 <= K_INPUT)||LA53_0==K_INT||(LA53_0 >= K_JSON && LA53_0 <= K_KEYS)||(LA53_0 >= K_KEYSPACES && LA53_0 <= K_LIKE)||(LA53_0 >= K_LIST && LA53_0 <= K_MAP)||LA53_0==K_NOLOGIN||LA53_0==K_NOSUPERUSER||LA53_0==K_OPTIONS||(LA53_0 >= K_PARTITION && LA53_0 <= K_PERMISSIONS)||LA53_0==K_RETURNS||(LA53_0 >= K_ROLE && LA53_0 <= K_ROLES)||(LA53_0 >= K_SFUNC && LA53_0 <= K_TINYINT)||LA53_0==K_TRIGGER||(LA53_0 >= K_TTL && LA53_0 <= K_TYPE)||(LA53_0 >= K_USER && LA53_0 <= K_USERS)||(LA53_0 >= K_UUID && LA53_0 <= K_VARINT)||LA53_0==K_WRITETIME||LA53_0==QUOTED_NAME) ) {
						alt53=2;
					}

					else {
						if (state.backtracking>0) {state.failed=true; return expr;}
						NoViableAltException nvae =
							new NoViableAltException("", 53, 0, input);
						throw nvae;
					}

					switch (alt53) {
						case 1 :
							// Parser.g:545:16: K_EXISTS
							{
							match(input,K_EXISTS,FOLLOW_K_EXISTS_in_updateStatement3546); if (state.failed) return expr;
							if ( state.backtracking==0 ) { ifExists = true; }
							}
							break;
						case 2 :
							// Parser.g:545:48: conditions= updateConditions
							{
							pushFollow(FOLLOW_updateConditions_in_updateStatement3554);
							conditions=updateConditions();
							state._fsp--;
							if (state.failed) return expr;
							}
							break;

					}

					}
					break;

			}

			if ( state.backtracking==0 ) {
			          expr = new UpdateStatement.ParsedUpdate(cf,
			                                                   attrs,
			                                                   operations,
			                                                   wclause.build(),
			                                                   conditions == null ? Collections.<Pair<ColumnMetadata.Raw, ColumnCondition.Raw>>emptyList() : conditions,
			                                                   ifExists);
			     }
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return expr;
	}
	// $ANTLR end "updateStatement"



	// $ANTLR start "updateConditions"
	// Parser.g:556:1: updateConditions returns [List<Pair<ColumnMetadata.Raw, ColumnCondition.Raw>> conditions] : columnCondition[conditions] ( K_AND columnCondition[conditions] )* ;
	public final List<Pair<ColumnMetadata.Raw, ColumnCondition.Raw>> updateConditions() throws RecognitionException {
		List<Pair<ColumnMetadata.Raw, ColumnCondition.Raw>> conditions = null;


		 conditions = new ArrayList<Pair<ColumnMetadata.Raw, ColumnCondition.Raw>>(); 
		try {
			// Parser.g:558:5: ( columnCondition[conditions] ( K_AND columnCondition[conditions] )* )
			// Parser.g:558:7: columnCondition[conditions] ( K_AND columnCondition[conditions] )*
			{
			pushFollow(FOLLOW_columnCondition_in_updateConditions3596);
			columnCondition(conditions);
			state._fsp--;
			if (state.failed) return conditions;
			// Parser.g:558:35: ( K_AND columnCondition[conditions] )*
			loop55:
			while (true) {
				int alt55=2;
				int LA55_0 = input.LA(1);
				if ( (LA55_0==K_AND) ) {
					alt55=1;
				}

				switch (alt55) {
				case 1 :
					// Parser.g:558:37: K_AND columnCondition[conditions]
					{
					match(input,K_AND,FOLLOW_K_AND_in_updateConditions3601); if (state.failed) return conditions;
					pushFollow(FOLLOW_columnCondition_in_updateConditions3603);
					columnCondition(conditions);
					state._fsp--;
					if (state.failed) return conditions;
					}
					break;

				default :
					break loop55;
				}
			}

			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return conditions;
	}
	// $ANTLR end "updateConditions"



	// $ANTLR start "deleteStatement"
	// Parser.g:569:1: deleteStatement returns [DeleteStatement.Parsed expr] : K_DELETE (dels= deleteSelection )? K_FROM cf= columnFamilyName ( usingClauseDelete[attrs] )? K_WHERE wclause= whereClause ( K_IF ( K_EXISTS |conditions= updateConditions ) )? ;
	public final DeleteStatement.Parsed deleteStatement() throws RecognitionException {
		DeleteStatement.Parsed expr = null;


		List<Operation.RawDeletion> dels =null;
		QualifiedName cf =null;
		WhereClause.Builder wclause =null;
		List<Pair<ColumnMetadata.Raw, ColumnCondition.Raw>> conditions =null;


		        Attributes.Raw attrs = new Attributes.Raw();
		        List<Operation.RawDeletion> columnDeletions = Collections.emptyList();
		        boolean ifExists = false;
		    
		try {
			// Parser.g:575:5: ( K_DELETE (dels= deleteSelection )? K_FROM cf= columnFamilyName ( usingClauseDelete[attrs] )? K_WHERE wclause= whereClause ( K_IF ( K_EXISTS |conditions= updateConditions ) )? )
			// Parser.g:575:7: K_DELETE (dels= deleteSelection )? K_FROM cf= columnFamilyName ( usingClauseDelete[attrs] )? K_WHERE wclause= whereClause ( K_IF ( K_EXISTS |conditions= updateConditions ) )?
			{
			match(input,K_DELETE,FOLLOW_K_DELETE_in_deleteStatement3640); if (state.failed) return expr;
			// Parser.g:575:16: (dels= deleteSelection )?
			int alt56=2;
			int LA56_0 = input.LA(1);
			if ( (LA56_0==EMPTY_QUOTED_NAME||LA56_0==IDENT||(LA56_0 >= K_AGGREGATE && LA56_0 <= K_ALL)||LA56_0==K_AS||LA56_0==K_ASCII||(LA56_0 >= K_BIGINT && LA56_0 <= K_BOOLEAN)||(LA56_0 >= K_CALLED && LA56_0 <= K_CLUSTERING)||(LA56_0 >= K_COMPACT && LA56_0 <= K_COUNTER)||LA56_0==K_CUSTOM||(LA56_0 >= K_DATE && LA56_0 <= K_DECIMAL)||(LA56_0 >= K_DISTINCT && LA56_0 <= K_DOUBLE)||LA56_0==K_DURATION||(LA56_0 >= K_EXISTS && LA56_0 <= K_FLOAT)||LA56_0==K_FROZEN||(LA56_0 >= K_FUNCTION && LA56_0 <= K_FUNCTIONS)||LA56_0==K_GROUP||(LA56_0 >= K_INET && LA56_0 <= K_INPUT)||LA56_0==K_INT||(LA56_0 >= K_JSON && LA56_0 <= K_KEYS)||(LA56_0 >= K_KEYSPACES && LA56_0 <= K_LIKE)||(LA56_0 >= K_LIST && LA56_0 <= K_MAP)||LA56_0==K_NOLOGIN||LA56_0==K_NOSUPERUSER||LA56_0==K_OPTIONS||(LA56_0 >= K_PARTITION && LA56_0 <= K_PERMISSIONS)||LA56_0==K_RETURNS||(LA56_0 >= K_ROLE && LA56_0 <= K_ROLES)||(LA56_0 >= K_SFUNC && LA56_0 <= K_TINYINT)||LA56_0==K_TRIGGER||(LA56_0 >= K_TTL && LA56_0 <= K_TYPE)||(LA56_0 >= K_USER && LA56_0 <= K_USERS)||(LA56_0 >= K_UUID && LA56_0 <= K_VARINT)||LA56_0==K_WRITETIME||LA56_0==QUOTED_NAME) ) {
				alt56=1;
			}
			switch (alt56) {
				case 1 :
					// Parser.g:575:18: dels= deleteSelection
					{
					pushFollow(FOLLOW_deleteSelection_in_deleteStatement3646);
					dels=deleteSelection();
					state._fsp--;
					if (state.failed) return expr;
					if ( state.backtracking==0 ) { columnDeletions = dels; }
					}
					break;

			}

			match(input,K_FROM,FOLLOW_K_FROM_in_deleteStatement3659); if (state.failed) return expr;
			pushFollow(FOLLOW_columnFamilyName_in_deleteStatement3663);
			cf=columnFamilyName();
			state._fsp--;
			if (state.failed) return expr;
			// Parser.g:577:7: ( usingClauseDelete[attrs] )?
			int alt57=2;
			int LA57_0 = input.LA(1);
			if ( (LA57_0==K_USING) ) {
				alt57=1;
			}
			switch (alt57) {
				case 1 :
					// Parser.g:577:9: usingClauseDelete[attrs]
					{
					pushFollow(FOLLOW_usingClauseDelete_in_deleteStatement3673);
					usingClauseDelete(attrs);
					state._fsp--;
					if (state.failed) return expr;
					}
					break;

			}

			match(input,K_WHERE,FOLLOW_K_WHERE_in_deleteStatement3685); if (state.failed) return expr;
			pushFollow(FOLLOW_whereClause_in_deleteStatement3689);
			wclause=whereClause();
			state._fsp--;
			if (state.failed) return expr;
			// Parser.g:579:7: ( K_IF ( K_EXISTS |conditions= updateConditions ) )?
			int alt59=2;
			int LA59_0 = input.LA(1);
			if ( (LA59_0==K_IF) ) {
				alt59=1;
			}
			switch (alt59) {
				case 1 :
					// Parser.g:579:9: K_IF ( K_EXISTS |conditions= updateConditions )
					{
					match(input,K_IF,FOLLOW_K_IF_in_deleteStatement3699); if (state.failed) return expr;
					// Parser.g:579:14: ( K_EXISTS |conditions= updateConditions )
					int alt58=2;
					int LA58_0 = input.LA(1);
					if ( (LA58_0==K_EXISTS) ) {
						int LA58_1 = input.LA(2);
						if ( (LA58_1==EOF||LA58_1==K_APPLY||LA58_1==K_DELETE||LA58_1==K_INSERT||LA58_1==K_UPDATE||LA58_1==200) ) {
							alt58=1;
						}
						else if ( (LA58_1==K_IN||LA58_1==188||LA58_1==197||(LA58_1 >= 201 && LA58_1 <= 206)) ) {
							alt58=2;
						}

						else {
							if (state.backtracking>0) {state.failed=true; return expr;}
							int nvaeMark = input.mark();
							try {
								input.consume();
								NoViableAltException nvae =
									new NoViableAltException("", 58, 1, input);
								throw nvae;
							} finally {
								input.rewind(nvaeMark);
							}
						}

					}
					else if ( (LA58_0==EMPTY_QUOTED_NAME||LA58_0==IDENT||(LA58_0 >= K_AGGREGATE && LA58_0 <= K_ALL)||LA58_0==K_AS||LA58_0==K_ASCII||(LA58_0 >= K_BIGINT && LA58_0 <= K_BOOLEAN)||(LA58_0 >= K_CALLED && LA58_0 <= K_CLUSTERING)||(LA58_0 >= K_COMPACT && LA58_0 <= K_COUNTER)||LA58_0==K_CUSTOM||(LA58_0 >= K_DATE && LA58_0 <= K_DECIMAL)||(LA58_0 >= K_DISTINCT && LA58_0 <= K_DOUBLE)||LA58_0==K_DURATION||(LA58_0 >= K_FILTERING && LA58_0 <= K_FLOAT)||LA58_0==K_FROZEN||(LA58_0 >= K_FUNCTION && LA58_0 <= K_FUNCTIONS)||LA58_0==K_GROUP||(LA58_0 >= K_INET && LA58_0 <= K_INPUT)||LA58_0==K_INT||(LA58_0 >= K_JSON && LA58_0 <= K_KEYS)||(LA58_0 >= K_KEYSPACES && LA58_0 <= K_LIKE)||(LA58_0 >= K_LIST && LA58_0 <= K_MAP)||LA58_0==K_NOLOGIN||LA58_0==K_NOSUPERUSER||LA58_0==K_OPTIONS||(LA58_0 >= K_PARTITION && LA58_0 <= K_PERMISSIONS)||LA58_0==K_RETURNS||(LA58_0 >= K_ROLE && LA58_0 <= K_ROLES)||(LA58_0 >= K_SFUNC && LA58_0 <= K_TINYINT)||LA58_0==K_TRIGGER||(LA58_0 >= K_TTL && LA58_0 <= K_TYPE)||(LA58_0 >= K_USER && LA58_0 <= K_USERS)||(LA58_0 >= K_UUID && LA58_0 <= K_VARINT)||LA58_0==K_WRITETIME||LA58_0==QUOTED_NAME) ) {
						alt58=2;
					}

					else {
						if (state.backtracking>0) {state.failed=true; return expr;}
						NoViableAltException nvae =
							new NoViableAltException("", 58, 0, input);
						throw nvae;
					}

					switch (alt58) {
						case 1 :
							// Parser.g:579:16: K_EXISTS
							{
							match(input,K_EXISTS,FOLLOW_K_EXISTS_in_deleteStatement3703); if (state.failed) return expr;
							if ( state.backtracking==0 ) { ifExists = true; }
							}
							break;
						case 2 :
							// Parser.g:579:48: conditions= updateConditions
							{
							pushFollow(FOLLOW_updateConditions_in_deleteStatement3711);
							conditions=updateConditions();
							state._fsp--;
							if (state.failed) return expr;
							}
							break;

					}

					}
					break;

			}

			if ( state.backtracking==0 ) {
			          expr = new DeleteStatement.Parsed(cf,
			                                             attrs,
			                                             columnDeletions,
			                                             wclause.build(),
			                                             conditions == null ? Collections.<Pair<ColumnMetadata.Raw, ColumnCondition.Raw>>emptyList() : conditions,
			                                             ifExists);
			      }
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return expr;
	}
	// $ANTLR end "deleteStatement"



	// $ANTLR start "deleteSelection"
	// Parser.g:590:1: deleteSelection returns [List<Operation.RawDeletion> operations] :t1= deleteOp ( ',' tN= deleteOp )* ;
	public final List<Operation.RawDeletion> deleteSelection() throws RecognitionException {
		List<Operation.RawDeletion> operations = null;


		Operation.RawDeletion t1 =null;
		Operation.RawDeletion tN =null;

		try {
			// Parser.g:591:5: (t1= deleteOp ( ',' tN= deleteOp )* )
			// Parser.g:591:7: t1= deleteOp ( ',' tN= deleteOp )*
			{
			if ( state.backtracking==0 ) { operations = new ArrayList<Operation.RawDeletion>(); }
			pushFollow(FOLLOW_deleteOp_in_deleteSelection3758);
			t1=deleteOp();
			state._fsp--;
			if (state.failed) return operations;
			if ( state.backtracking==0 ) { operations.add(t1); }
			// Parser.g:593:11: ( ',' tN= deleteOp )*
			loop60:
			while (true) {
				int alt60=2;
				int LA60_0 = input.LA(1);
				if ( (LA60_0==194) ) {
					alt60=1;
				}

				switch (alt60) {
				case 1 :
					// Parser.g:593:12: ',' tN= deleteOp
					{
					match(input,194,FOLLOW_194_in_deleteSelection3773); if (state.failed) return operations;
					pushFollow(FOLLOW_deleteOp_in_deleteSelection3777);
					tN=deleteOp();
					state._fsp--;
					if (state.failed) return operations;
					if ( state.backtracking==0 ) { operations.add(tN); }
					}
					break;

				default :
					break loop60;
				}
			}

			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return operations;
	}
	// $ANTLR end "deleteSelection"



	// $ANTLR start "deleteOp"
	// Parser.g:596:1: deleteOp returns [Operation.RawDeletion op] : (c= cident |c= cident '[' t= term ']' |c= cident '.' field= fident );
	public final Operation.RawDeletion deleteOp() throws RecognitionException {
		Operation.RawDeletion op = null;


		ColumnMetadata.Raw c =null;
		Term.Raw t =null;
		FieldIdentifier field =null;

		try {
			// Parser.g:597:5: (c= cident |c= cident '[' t= term ']' |c= cident '.' field= fident )
			int alt61=3;
			alt61 = dfa61.predict(input);
			switch (alt61) {
				case 1 :
					// Parser.g:597:7: c= cident
					{
					pushFollow(FOLLOW_cident_in_deleteOp3804);
					c=cident();
					state._fsp--;
					if (state.failed) return op;
					if ( state.backtracking==0 ) { op = new Operation.ColumnDeletion(c); }
					}
					break;
				case 2 :
					// Parser.g:598:7: c= cident '[' t= term ']'
					{
					pushFollow(FOLLOW_cident_in_deleteOp3831);
					c=cident();
					state._fsp--;
					if (state.failed) return op;
					match(input,206,FOLLOW_206_in_deleteOp3833); if (state.failed) return op;
					pushFollow(FOLLOW_term_in_deleteOp3837);
					t=term();
					state._fsp--;
					if (state.failed) return op;
					match(input,208,FOLLOW_208_in_deleteOp3839); if (state.failed) return op;
					if ( state.backtracking==0 ) { op = new Operation.ElementDeletion(c, t); }
					}
					break;
				case 3 :
					// Parser.g:599:7: c= cident '.' field= fident
					{
					pushFollow(FOLLOW_cident_in_deleteOp3851);
					c=cident();
					state._fsp--;
					if (state.failed) return op;
					match(input,197,FOLLOW_197_in_deleteOp3853); if (state.failed) return op;
					pushFollow(FOLLOW_fident_in_deleteOp3857);
					field=fident();
					state._fsp--;
					if (state.failed) return op;
					if ( state.backtracking==0 ) { op = new Operation.FieldDeletion(c, field); }
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return op;
	}
	// $ANTLR end "deleteOp"



	// $ANTLR start "usingClauseDelete"
	// Parser.g:602:1: usingClauseDelete[Attributes.Raw attrs] : K_USING K_TIMESTAMP ts= intValue ;
	public final void usingClauseDelete(Attributes.Raw attrs) throws RecognitionException {
		Term.Raw ts =null;

		try {
			// Parser.g:603:5: ( K_USING K_TIMESTAMP ts= intValue )
			// Parser.g:603:7: K_USING K_TIMESTAMP ts= intValue
			{
			match(input,K_USING,FOLLOW_K_USING_in_usingClauseDelete3877); if (state.failed) return;
			match(input,K_TIMESTAMP,FOLLOW_K_TIMESTAMP_in_usingClauseDelete3879); if (state.failed) return;
			pushFollow(FOLLOW_intValue_in_usingClauseDelete3883);
			ts=intValue();
			state._fsp--;
			if (state.failed) return;
			if ( state.backtracking==0 ) { attrs.timestamp = ts; }
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "usingClauseDelete"



	// $ANTLR start "batchStatement"
	// Parser.g:630:1: batchStatement returns [BatchStatement.Parsed expr] : K_BEGIN ( K_UNLOGGED | K_COUNTER )? K_BATCH ( usingClause[attrs] )? (s= batchStatementObjective ( ';' )? )* K_APPLY K_BATCH ;
	public final BatchStatement.Parsed batchStatement() throws RecognitionException {
		BatchStatement.Parsed expr = null;


		ModificationStatement.Parsed s =null;


		        BatchStatement.Type type = BatchStatement.Type.LOGGED;
		        List<ModificationStatement.Parsed> statements = new ArrayList<ModificationStatement.Parsed>();
		        Attributes.Raw attrs = new Attributes.Raw();
		    
		try {
			// Parser.g:636:5: ( K_BEGIN ( K_UNLOGGED | K_COUNTER )? K_BATCH ( usingClause[attrs] )? (s= batchStatementObjective ( ';' )? )* K_APPLY K_BATCH )
			// Parser.g:636:7: K_BEGIN ( K_UNLOGGED | K_COUNTER )? K_BATCH ( usingClause[attrs] )? (s= batchStatementObjective ( ';' )? )* K_APPLY K_BATCH
			{
			match(input,K_BEGIN,FOLLOW_K_BEGIN_in_batchStatement3917); if (state.failed) return expr;
			// Parser.g:637:7: ( K_UNLOGGED | K_COUNTER )?
			int alt62=3;
			int LA62_0 = input.LA(1);
			if ( (LA62_0==K_UNLOGGED) ) {
				alt62=1;
			}
			else if ( (LA62_0==K_COUNTER) ) {
				alt62=2;
			}
			switch (alt62) {
				case 1 :
					// Parser.g:637:9: K_UNLOGGED
					{
					match(input,K_UNLOGGED,FOLLOW_K_UNLOGGED_in_batchStatement3927); if (state.failed) return expr;
					if ( state.backtracking==0 ) { type = BatchStatement.Type.UNLOGGED; }
					}
					break;
				case 2 :
					// Parser.g:637:63: K_COUNTER
					{
					match(input,K_COUNTER,FOLLOW_K_COUNTER_in_batchStatement3933); if (state.failed) return expr;
					if ( state.backtracking==0 ) { type = BatchStatement.Type.COUNTER; }
					}
					break;

			}

			match(input,K_BATCH,FOLLOW_K_BATCH_in_batchStatement3946); if (state.failed) return expr;
			// Parser.g:638:15: ( usingClause[attrs] )?
			int alt63=2;
			int LA63_0 = input.LA(1);
			if ( (LA63_0==K_USING) ) {
				alt63=1;
			}
			switch (alt63) {
				case 1 :
					// Parser.g:638:17: usingClause[attrs]
					{
					pushFollow(FOLLOW_usingClause_in_batchStatement3950);
					usingClause(attrs);
					state._fsp--;
					if (state.failed) return expr;
					}
					break;

			}

			// Parser.g:639:11: (s= batchStatementObjective ( ';' )? )*
			loop65:
			while (true) {
				int alt65=2;
				int LA65_0 = input.LA(1);
				if ( (LA65_0==K_DELETE||LA65_0==K_INSERT||LA65_0==K_UPDATE) ) {
					alt65=1;
				}

				switch (alt65) {
				case 1 :
					// Parser.g:639:13: s= batchStatementObjective ( ';' )?
					{
					pushFollow(FOLLOW_batchStatementObjective_in_batchStatement3970);
					s=batchStatementObjective();
					state._fsp--;
					if (state.failed) return expr;
					// Parser.g:639:39: ( ';' )?
					int alt64=2;
					int LA64_0 = input.LA(1);
					if ( (LA64_0==200) ) {
						alt64=1;
					}
					switch (alt64) {
						case 1 :
							// Parser.g:639:39: ';'
							{
							match(input,200,FOLLOW_200_in_batchStatement3972); if (state.failed) return expr;
							}
							break;

					}

					if ( state.backtracking==0 ) { statements.add(s); }
					}
					break;

				default :
					break loop65;
				}
			}

			match(input,K_APPLY,FOLLOW_K_APPLY_in_batchStatement3986); if (state.failed) return expr;
			match(input,K_BATCH,FOLLOW_K_BATCH_in_batchStatement3988); if (state.failed) return expr;
			if ( state.backtracking==0 ) {
			          expr = new BatchStatement.Parsed(type, attrs, statements);
			      }
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return expr;
	}
	// $ANTLR end "batchStatement"



	// $ANTLR start "batchStatementObjective"
	// Parser.g:646:1: batchStatementObjective returns [ModificationStatement.Parsed statement] : (i= insertStatement |u= updateStatement |d= deleteStatement );
	public final ModificationStatement.Parsed batchStatementObjective() throws RecognitionException {
		ModificationStatement.Parsed statement = null;


		ModificationStatement.Parsed i =null;
		UpdateStatement.ParsedUpdate u =null;
		DeleteStatement.Parsed d =null;

		try {
			// Parser.g:647:5: (i= insertStatement |u= updateStatement |d= deleteStatement )
			int alt66=3;
			switch ( input.LA(1) ) {
			case K_INSERT:
				{
				alt66=1;
				}
				break;
			case K_UPDATE:
				{
				alt66=2;
				}
				break;
			case K_DELETE:
				{
				alt66=3;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return statement;}
				NoViableAltException nvae =
					new NoViableAltException("", 66, 0, input);
				throw nvae;
			}
			switch (alt66) {
				case 1 :
					// Parser.g:647:7: i= insertStatement
					{
					pushFollow(FOLLOW_insertStatement_in_batchStatementObjective4019);
					i=insertStatement();
					state._fsp--;
					if (state.failed) return statement;
					if ( state.backtracking==0 ) { statement = i; }
					}
					break;
				case 2 :
					// Parser.g:648:7: u= updateStatement
					{
					pushFollow(FOLLOW_updateStatement_in_batchStatementObjective4032);
					u=updateStatement();
					state._fsp--;
					if (state.failed) return statement;
					if ( state.backtracking==0 ) { statement = u; }
					}
					break;
				case 3 :
					// Parser.g:649:7: d= deleteStatement
					{
					pushFollow(FOLLOW_deleteStatement_in_batchStatementObjective4045);
					d=deleteStatement();
					state._fsp--;
					if (state.failed) return statement;
					if ( state.backtracking==0 ) { statement = d; }
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return statement;
	}
	// $ANTLR end "batchStatementObjective"



	// $ANTLR start "createAggregateStatement"
	// Parser.g:652:1: createAggregateStatement returns [CreateAggregateStatement.Raw stmt] : K_CREATE ( K_OR K_REPLACE )? K_AGGREGATE ( K_IF K_NOT K_EXISTS )? fn= functionName '(' (v= comparatorType ( ',' v= comparatorType )* )? ')' K_SFUNC sfunc= allowedFunctionName K_STYPE stype= comparatorType ( K_FINALFUNC ffunc= allowedFunctionName )? ( K_INITCOND ival= term )? ;
	public final CreateAggregateStatement.Raw createAggregateStatement() throws RecognitionException {
		CreateAggregateStatement.Raw stmt = null;


		FunctionName fn =null;
		CQL3Type.Raw v =null;
		String sfunc =null;
		CQL3Type.Raw stype =null;
		String ffunc =null;
		Term.Raw ival =null;


		        boolean orReplace = false;
		        boolean ifNotExists = false;

		        List<CQL3Type.Raw> argTypes = new ArrayList<>();
		    
		try {
			// Parser.g:659:5: ( K_CREATE ( K_OR K_REPLACE )? K_AGGREGATE ( K_IF K_NOT K_EXISTS )? fn= functionName '(' (v= comparatorType ( ',' v= comparatorType )* )? ')' K_SFUNC sfunc= allowedFunctionName K_STYPE stype= comparatorType ( K_FINALFUNC ffunc= allowedFunctionName )? ( K_INITCOND ival= term )? )
			// Parser.g:659:7: K_CREATE ( K_OR K_REPLACE )? K_AGGREGATE ( K_IF K_NOT K_EXISTS )? fn= functionName '(' (v= comparatorType ( ',' v= comparatorType )* )? ')' K_SFUNC sfunc= allowedFunctionName K_STYPE stype= comparatorType ( K_FINALFUNC ffunc= allowedFunctionName )? ( K_INITCOND ival= term )?
			{
			match(input,K_CREATE,FOLLOW_K_CREATE_in_createAggregateStatement4078); if (state.failed) return stmt;
			// Parser.g:659:16: ( K_OR K_REPLACE )?
			int alt67=2;
			int LA67_0 = input.LA(1);
			if ( (LA67_0==K_OR) ) {
				alt67=1;
			}
			switch (alt67) {
				case 1 :
					// Parser.g:659:17: K_OR K_REPLACE
					{
					match(input,K_OR,FOLLOW_K_OR_in_createAggregateStatement4081); if (state.failed) return stmt;
					match(input,K_REPLACE,FOLLOW_K_REPLACE_in_createAggregateStatement4083); if (state.failed) return stmt;
					if ( state.backtracking==0 ) { orReplace = true; }
					}
					break;

			}

			match(input,K_AGGREGATE,FOLLOW_K_AGGREGATE_in_createAggregateStatement4095); if (state.failed) return stmt;
			// Parser.g:661:7: ( K_IF K_NOT K_EXISTS )?
			int alt68=2;
			int LA68_0 = input.LA(1);
			if ( (LA68_0==K_IF) ) {
				alt68=1;
			}
			switch (alt68) {
				case 1 :
					// Parser.g:661:8: K_IF K_NOT K_EXISTS
					{
					match(input,K_IF,FOLLOW_K_IF_in_createAggregateStatement4104); if (state.failed) return stmt;
					match(input,K_NOT,FOLLOW_K_NOT_in_createAggregateStatement4106); if (state.failed) return stmt;
					match(input,K_EXISTS,FOLLOW_K_EXISTS_in_createAggregateStatement4108); if (state.failed) return stmt;
					if ( state.backtracking==0 ) { ifNotExists = true; }
					}
					break;

			}

			pushFollow(FOLLOW_functionName_in_createAggregateStatement4122);
			fn=functionName();
			state._fsp--;
			if (state.failed) return stmt;
			match(input,190,FOLLOW_190_in_createAggregateStatement4130); if (state.failed) return stmt;
			// Parser.g:664:9: (v= comparatorType ( ',' v= comparatorType )* )?
			int alt70=2;
			int LA70_0 = input.LA(1);
			if ( (LA70_0==IDENT||(LA70_0 >= K_AGGREGATE && LA70_0 <= K_ALL)||LA70_0==K_AS||LA70_0==K_ASCII||(LA70_0 >= K_BIGINT && LA70_0 <= K_BOOLEAN)||(LA70_0 >= K_CALLED && LA70_0 <= K_CLUSTERING)||(LA70_0 >= K_COMPACT && LA70_0 <= K_COUNTER)||LA70_0==K_CUSTOM||(LA70_0 >= K_DATE && LA70_0 <= K_DECIMAL)||(LA70_0 >= K_DISTINCT && LA70_0 <= K_DOUBLE)||LA70_0==K_DURATION||(LA70_0 >= K_EXISTS && LA70_0 <= K_FLOAT)||LA70_0==K_FROZEN||(LA70_0 >= K_FUNCTION && LA70_0 <= K_FUNCTIONS)||LA70_0==K_GROUP||(LA70_0 >= K_INET && LA70_0 <= K_INPUT)||LA70_0==K_INT||(LA70_0 >= K_JSON && LA70_0 <= K_KEYS)||(LA70_0 >= K_KEYSPACES && LA70_0 <= K_LIKE)||(LA70_0 >= K_LIST && LA70_0 <= K_MAP)||LA70_0==K_NOLOGIN||LA70_0==K_NOSUPERUSER||LA70_0==K_OPTIONS||(LA70_0 >= K_PARTITION && LA70_0 <= K_PERMISSIONS)||LA70_0==K_RETURNS||(LA70_0 >= K_ROLE && LA70_0 <= K_ROLES)||(LA70_0 >= K_SET && LA70_0 <= K_TINYINT)||LA70_0==K_TRIGGER||(LA70_0 >= K_TTL && LA70_0 <= K_TYPE)||(LA70_0 >= K_USER && LA70_0 <= K_USERS)||(LA70_0 >= K_UUID && LA70_0 <= K_VARINT)||LA70_0==K_WRITETIME||LA70_0==QUOTED_NAME||LA70_0==STRING_LITERAL) ) {
				alt70=1;
			}
			switch (alt70) {
				case 1 :
					// Parser.g:665:11: v= comparatorType ( ',' v= comparatorType )*
					{
					pushFollow(FOLLOW_comparatorType_in_createAggregateStatement4154);
					v=comparatorType();
					state._fsp--;
					if (state.failed) return stmt;
					if ( state.backtracking==0 ) { argTypes.add(v); }
					// Parser.g:666:11: ( ',' v= comparatorType )*
					loop69:
					while (true) {
						int alt69=2;
						int LA69_0 = input.LA(1);
						if ( (LA69_0==194) ) {
							alt69=1;
						}

						switch (alt69) {
						case 1 :
							// Parser.g:666:13: ',' v= comparatorType
							{
							match(input,194,FOLLOW_194_in_createAggregateStatement4170); if (state.failed) return stmt;
							pushFollow(FOLLOW_comparatorType_in_createAggregateStatement4174);
							v=comparatorType();
							state._fsp--;
							if (state.failed) return stmt;
							if ( state.backtracking==0 ) { argTypes.add(v); }
							}
							break;

						default :
							break loop69;
						}
					}

					}
					break;

			}

			match(input,191,FOLLOW_191_in_createAggregateStatement4198); if (state.failed) return stmt;
			match(input,K_SFUNC,FOLLOW_K_SFUNC_in_createAggregateStatement4206); if (state.failed) return stmt;
			pushFollow(FOLLOW_allowedFunctionName_in_createAggregateStatement4212);
			sfunc=allowedFunctionName();
			state._fsp--;
			if (state.failed) return stmt;
			match(input,K_STYPE,FOLLOW_K_STYPE_in_createAggregateStatement4220); if (state.failed) return stmt;
			pushFollow(FOLLOW_comparatorType_in_createAggregateStatement4226);
			stype=comparatorType();
			state._fsp--;
			if (state.failed) return stmt;
			// Parser.g:671:7: ( K_FINALFUNC ffunc= allowedFunctionName )?
			int alt71=2;
			int LA71_0 = input.LA(1);
			if ( (LA71_0==K_FINALFUNC) ) {
				alt71=1;
			}
			switch (alt71) {
				case 1 :
					// Parser.g:672:9: K_FINALFUNC ffunc= allowedFunctionName
					{
					match(input,K_FINALFUNC,FOLLOW_K_FINALFUNC_in_createAggregateStatement4244); if (state.failed) return stmt;
					pushFollow(FOLLOW_allowedFunctionName_in_createAggregateStatement4250);
					ffunc=allowedFunctionName();
					state._fsp--;
					if (state.failed) return stmt;
					}
					break;

			}

			// Parser.g:674:7: ( K_INITCOND ival= term )?
			int alt72=2;
			int LA72_0 = input.LA(1);
			if ( (LA72_0==K_INITCOND) ) {
				alt72=1;
			}
			switch (alt72) {
				case 1 :
					// Parser.g:675:9: K_INITCOND ival= term
					{
					match(input,K_INITCOND,FOLLOW_K_INITCOND_in_createAggregateStatement4277); if (state.failed) return stmt;
					pushFollow(FOLLOW_term_in_createAggregateStatement4283);
					ival=term();
					state._fsp--;
					if (state.failed) return stmt;
					}
					break;

			}

			if ( state.backtracking==0 ) { stmt = new CreateAggregateStatement.Raw(fn, argTypes, stype, sfunc, ffunc, ival, orReplace, ifNotExists); }
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return stmt;
	}
	// $ANTLR end "createAggregateStatement"



	// $ANTLR start "dropAggregateStatement"
	// Parser.g:680:1: dropAggregateStatement returns [DropAggregateStatement.Raw stmt] : K_DROP K_AGGREGATE ( K_IF K_EXISTS )? fn= functionName ( '(' (v= comparatorType ( ',' v= comparatorType )* )? ')' )? ;
	public final DropAggregateStatement.Raw dropAggregateStatement() throws RecognitionException {
		DropAggregateStatement.Raw stmt = null;


		FunctionName fn =null;
		CQL3Type.Raw v =null;


		        boolean ifExists = false;
		        List<CQL3Type.Raw> argTypes = new ArrayList<>();
		        boolean argsSpecified = false;
		    
		try {
			// Parser.g:686:5: ( K_DROP K_AGGREGATE ( K_IF K_EXISTS )? fn= functionName ( '(' (v= comparatorType ( ',' v= comparatorType )* )? ')' )? )
			// Parser.g:686:7: K_DROP K_AGGREGATE ( K_IF K_EXISTS )? fn= functionName ( '(' (v= comparatorType ( ',' v= comparatorType )* )? ')' )?
			{
			match(input,K_DROP,FOLLOW_K_DROP_in_dropAggregateStatement4330); if (state.failed) return stmt;
			match(input,K_AGGREGATE,FOLLOW_K_AGGREGATE_in_dropAggregateStatement4332); if (state.failed) return stmt;
			// Parser.g:687:7: ( K_IF K_EXISTS )?
			int alt73=2;
			int LA73_0 = input.LA(1);
			if ( (LA73_0==K_IF) ) {
				alt73=1;
			}
			switch (alt73) {
				case 1 :
					// Parser.g:687:8: K_IF K_EXISTS
					{
					match(input,K_IF,FOLLOW_K_IF_in_dropAggregateStatement4341); if (state.failed) return stmt;
					match(input,K_EXISTS,FOLLOW_K_EXISTS_in_dropAggregateStatement4343); if (state.failed) return stmt;
					if ( state.backtracking==0 ) { ifExists = true; }
					}
					break;

			}

			pushFollow(FOLLOW_functionName_in_dropAggregateStatement4358);
			fn=functionName();
			state._fsp--;
			if (state.failed) return stmt;
			// Parser.g:689:7: ( '(' (v= comparatorType ( ',' v= comparatorType )* )? ')' )?
			int alt76=2;
			int LA76_0 = input.LA(1);
			if ( (LA76_0==190) ) {
				alt76=1;
			}
			switch (alt76) {
				case 1 :
					// Parser.g:690:9: '(' (v= comparatorType ( ',' v= comparatorType )* )? ')'
					{
					match(input,190,FOLLOW_190_in_dropAggregateStatement4376); if (state.failed) return stmt;
					// Parser.g:691:11: (v= comparatorType ( ',' v= comparatorType )* )?
					int alt75=2;
					int LA75_0 = input.LA(1);
					if ( (LA75_0==IDENT||(LA75_0 >= K_AGGREGATE && LA75_0 <= K_ALL)||LA75_0==K_AS||LA75_0==K_ASCII||(LA75_0 >= K_BIGINT && LA75_0 <= K_BOOLEAN)||(LA75_0 >= K_CALLED && LA75_0 <= K_CLUSTERING)||(LA75_0 >= K_COMPACT && LA75_0 <= K_COUNTER)||LA75_0==K_CUSTOM||(LA75_0 >= K_DATE && LA75_0 <= K_DECIMAL)||(LA75_0 >= K_DISTINCT && LA75_0 <= K_DOUBLE)||LA75_0==K_DURATION||(LA75_0 >= K_EXISTS && LA75_0 <= K_FLOAT)||LA75_0==K_FROZEN||(LA75_0 >= K_FUNCTION && LA75_0 <= K_FUNCTIONS)||LA75_0==K_GROUP||(LA75_0 >= K_INET && LA75_0 <= K_INPUT)||LA75_0==K_INT||(LA75_0 >= K_JSON && LA75_0 <= K_KEYS)||(LA75_0 >= K_KEYSPACES && LA75_0 <= K_LIKE)||(LA75_0 >= K_LIST && LA75_0 <= K_MAP)||LA75_0==K_NOLOGIN||LA75_0==K_NOSUPERUSER||LA75_0==K_OPTIONS||(LA75_0 >= K_PARTITION && LA75_0 <= K_PERMISSIONS)||LA75_0==K_RETURNS||(LA75_0 >= K_ROLE && LA75_0 <= K_ROLES)||(LA75_0 >= K_SET && LA75_0 <= K_TINYINT)||LA75_0==K_TRIGGER||(LA75_0 >= K_TTL && LA75_0 <= K_TYPE)||(LA75_0 >= K_USER && LA75_0 <= K_USERS)||(LA75_0 >= K_UUID && LA75_0 <= K_VARINT)||LA75_0==K_WRITETIME||LA75_0==QUOTED_NAME||LA75_0==STRING_LITERAL) ) {
						alt75=1;
					}
					switch (alt75) {
						case 1 :
							// Parser.g:692:13: v= comparatorType ( ',' v= comparatorType )*
							{
							pushFollow(FOLLOW_comparatorType_in_dropAggregateStatement4404);
							v=comparatorType();
							state._fsp--;
							if (state.failed) return stmt;
							if ( state.backtracking==0 ) { argTypes.add(v); }
							// Parser.g:693:13: ( ',' v= comparatorType )*
							loop74:
							while (true) {
								int alt74=2;
								int LA74_0 = input.LA(1);
								if ( (LA74_0==194) ) {
									alt74=1;
								}

								switch (alt74) {
								case 1 :
									// Parser.g:693:15: ',' v= comparatorType
									{
									match(input,194,FOLLOW_194_in_dropAggregateStatement4422); if (state.failed) return stmt;
									pushFollow(FOLLOW_comparatorType_in_dropAggregateStatement4426);
									v=comparatorType();
									state._fsp--;
									if (state.failed) return stmt;
									if ( state.backtracking==0 ) { argTypes.add(v); }
									}
									break;

								default :
									break loop74;
								}
							}

							}
							break;

					}

					match(input,191,FOLLOW_191_in_dropAggregateStatement4454); if (state.failed) return stmt;
					if ( state.backtracking==0 ) { argsSpecified = true; }
					}
					break;

			}

			if ( state.backtracking==0 ) { stmt = new DropAggregateStatement.Raw(fn, argTypes, argsSpecified, ifExists); }
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return stmt;
	}
	// $ANTLR end "dropAggregateStatement"



	// $ANTLR start "createFunctionStatement"
	// Parser.g:701:1: createFunctionStatement returns [CreateFunctionStatement.Raw stmt] : K_CREATE ( K_OR K_REPLACE )? K_FUNCTION ( K_IF K_NOT K_EXISTS )? fn= functionName '(' (k= noncol_ident v= comparatorType ( ',' k= noncol_ident v= comparatorType )* )? ')' ( ( K_RETURNS K_NULL ) | ( K_CALLED ) ) K_ON K_NULL K_INPUT K_RETURNS returnType= comparatorType K_LANGUAGE language= IDENT K_AS body= STRING_LITERAL ;
	public final CreateFunctionStatement.Raw createFunctionStatement() throws RecognitionException {
		CreateFunctionStatement.Raw stmt = null;


		Token language=null;
		Token body=null;
		FunctionName fn =null;
		ColumnIdentifier k =null;
		CQL3Type.Raw v =null;
		CQL3Type.Raw returnType =null;


		        boolean orReplace = false;
		        boolean ifNotExists = false;

		        List<ColumnIdentifier> argNames = new ArrayList<>();
		        List<CQL3Type.Raw> argTypes = new ArrayList<>();
		        boolean calledOnNullInput = false;
		    
		try {
			// Parser.g:710:5: ( K_CREATE ( K_OR K_REPLACE )? K_FUNCTION ( K_IF K_NOT K_EXISTS )? fn= functionName '(' (k= noncol_ident v= comparatorType ( ',' k= noncol_ident v= comparatorType )* )? ')' ( ( K_RETURNS K_NULL ) | ( K_CALLED ) ) K_ON K_NULL K_INPUT K_RETURNS returnType= comparatorType K_LANGUAGE language= IDENT K_AS body= STRING_LITERAL )
			// Parser.g:710:7: K_CREATE ( K_OR K_REPLACE )? K_FUNCTION ( K_IF K_NOT K_EXISTS )? fn= functionName '(' (k= noncol_ident v= comparatorType ( ',' k= noncol_ident v= comparatorType )* )? ')' ( ( K_RETURNS K_NULL ) | ( K_CALLED ) ) K_ON K_NULL K_INPUT K_RETURNS returnType= comparatorType K_LANGUAGE language= IDENT K_AS body= STRING_LITERAL
			{
			match(input,K_CREATE,FOLLOW_K_CREATE_in_createFunctionStatement4511); if (state.failed) return stmt;
			// Parser.g:710:16: ( K_OR K_REPLACE )?
			int alt77=2;
			int LA77_0 = input.LA(1);
			if ( (LA77_0==K_OR) ) {
				alt77=1;
			}
			switch (alt77) {
				case 1 :
					// Parser.g:710:17: K_OR K_REPLACE
					{
					match(input,K_OR,FOLLOW_K_OR_in_createFunctionStatement4514); if (state.failed) return stmt;
					match(input,K_REPLACE,FOLLOW_K_REPLACE_in_createFunctionStatement4516); if (state.failed) return stmt;
					if ( state.backtracking==0 ) { orReplace = true; }
					}
					break;

			}

			match(input,K_FUNCTION,FOLLOW_K_FUNCTION_in_createFunctionStatement4528); if (state.failed) return stmt;
			// Parser.g:712:7: ( K_IF K_NOT K_EXISTS )?
			int alt78=2;
			int LA78_0 = input.LA(1);
			if ( (LA78_0==K_IF) ) {
				alt78=1;
			}
			switch (alt78) {
				case 1 :
					// Parser.g:712:8: K_IF K_NOT K_EXISTS
					{
					match(input,K_IF,FOLLOW_K_IF_in_createFunctionStatement4537); if (state.failed) return stmt;
					match(input,K_NOT,FOLLOW_K_NOT_in_createFunctionStatement4539); if (state.failed) return stmt;
					match(input,K_EXISTS,FOLLOW_K_EXISTS_in_createFunctionStatement4541); if (state.failed) return stmt;
					if ( state.backtracking==0 ) { ifNotExists = true; }
					}
					break;

			}

			pushFollow(FOLLOW_functionName_in_createFunctionStatement4555);
			fn=functionName();
			state._fsp--;
			if (state.failed) return stmt;
			match(input,190,FOLLOW_190_in_createFunctionStatement4563); if (state.failed) return stmt;
			// Parser.g:715:9: (k= noncol_ident v= comparatorType ( ',' k= noncol_ident v= comparatorType )* )?
			int alt80=2;
			int LA80_0 = input.LA(1);
			if ( (LA80_0==IDENT||(LA80_0 >= K_AGGREGATE && LA80_0 <= K_ALL)||LA80_0==K_AS||LA80_0==K_ASCII||(LA80_0 >= K_BIGINT && LA80_0 <= K_BOOLEAN)||(LA80_0 >= K_CALLED && LA80_0 <= K_CLUSTERING)||(LA80_0 >= K_COMPACT && LA80_0 <= K_COUNTER)||LA80_0==K_CUSTOM||(LA80_0 >= K_DATE && LA80_0 <= K_DECIMAL)||(LA80_0 >= K_DISTINCT && LA80_0 <= K_DOUBLE)||LA80_0==K_DURATION||(LA80_0 >= K_EXISTS && LA80_0 <= K_FLOAT)||LA80_0==K_FROZEN||(LA80_0 >= K_FUNCTION && LA80_0 <= K_FUNCTIONS)||LA80_0==K_GROUP||(LA80_0 >= K_INET && LA80_0 <= K_INPUT)||LA80_0==K_INT||(LA80_0 >= K_JSON && LA80_0 <= K_KEYS)||(LA80_0 >= K_KEYSPACES && LA80_0 <= K_LIKE)||(LA80_0 >= K_LIST && LA80_0 <= K_MAP)||LA80_0==K_NOLOGIN||LA80_0==K_NOSUPERUSER||LA80_0==K_OPTIONS||(LA80_0 >= K_PARTITION && LA80_0 <= K_PERMISSIONS)||LA80_0==K_RETURNS||(LA80_0 >= K_ROLE && LA80_0 <= K_ROLES)||(LA80_0 >= K_SFUNC && LA80_0 <= K_TINYINT)||LA80_0==K_TRIGGER||(LA80_0 >= K_TTL && LA80_0 <= K_TYPE)||(LA80_0 >= K_USER && LA80_0 <= K_USERS)||(LA80_0 >= K_UUID && LA80_0 <= K_VARINT)||LA80_0==K_WRITETIME||LA80_0==QUOTED_NAME) ) {
				alt80=1;
			}
			switch (alt80) {
				case 1 :
					// Parser.g:716:11: k= noncol_ident v= comparatorType ( ',' k= noncol_ident v= comparatorType )*
					{
					pushFollow(FOLLOW_noncol_ident_in_createFunctionStatement4587);
					k=noncol_ident();
					state._fsp--;
					if (state.failed) return stmt;
					pushFollow(FOLLOW_comparatorType_in_createFunctionStatement4591);
					v=comparatorType();
					state._fsp--;
					if (state.failed) return stmt;
					if ( state.backtracking==0 ) { argNames.add(k); argTypes.add(v); }
					// Parser.g:717:11: ( ',' k= noncol_ident v= comparatorType )*
					loop79:
					while (true) {
						int alt79=2;
						int LA79_0 = input.LA(1);
						if ( (LA79_0==194) ) {
							alt79=1;
						}

						switch (alt79) {
						case 1 :
							// Parser.g:717:13: ',' k= noncol_ident v= comparatorType
							{
							match(input,194,FOLLOW_194_in_createFunctionStatement4607); if (state.failed) return stmt;
							pushFollow(FOLLOW_noncol_ident_in_createFunctionStatement4611);
							k=noncol_ident();
							state._fsp--;
							if (state.failed) return stmt;
							pushFollow(FOLLOW_comparatorType_in_createFunctionStatement4615);
							v=comparatorType();
							state._fsp--;
							if (state.failed) return stmt;
							if ( state.backtracking==0 ) { argNames.add(k); argTypes.add(v); }
							}
							break;

						default :
							break loop79;
						}
					}

					}
					break;

			}

			match(input,191,FOLLOW_191_in_createFunctionStatement4639); if (state.failed) return stmt;
			// Parser.g:720:7: ( ( K_RETURNS K_NULL ) | ( K_CALLED ) )
			int alt81=2;
			int LA81_0 = input.LA(1);
			if ( (LA81_0==K_RETURNS) ) {
				alt81=1;
			}
			else if ( (LA81_0==K_CALLED) ) {
				alt81=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return stmt;}
				NoViableAltException nvae =
					new NoViableAltException("", 81, 0, input);
				throw nvae;
			}

			switch (alt81) {
				case 1 :
					// Parser.g:720:9: ( K_RETURNS K_NULL )
					{
					// Parser.g:720:9: ( K_RETURNS K_NULL )
					// Parser.g:720:10: K_RETURNS K_NULL
					{
					match(input,K_RETURNS,FOLLOW_K_RETURNS_in_createFunctionStatement4650); if (state.failed) return stmt;
					match(input,K_NULL,FOLLOW_K_NULL_in_createFunctionStatement4652); if (state.failed) return stmt;
					}

					}
					break;
				case 2 :
					// Parser.g:720:30: ( K_CALLED )
					{
					// Parser.g:720:30: ( K_CALLED )
					// Parser.g:720:31: K_CALLED
					{
					match(input,K_CALLED,FOLLOW_K_CALLED_in_createFunctionStatement4658); if (state.failed) return stmt;
					if ( state.backtracking==0 ) { calledOnNullInput=true; }
					}

					}
					break;

			}

			match(input,K_ON,FOLLOW_K_ON_in_createFunctionStatement4664); if (state.failed) return stmt;
			match(input,K_NULL,FOLLOW_K_NULL_in_createFunctionStatement4666); if (state.failed) return stmt;
			match(input,K_INPUT,FOLLOW_K_INPUT_in_createFunctionStatement4668); if (state.failed) return stmt;
			match(input,K_RETURNS,FOLLOW_K_RETURNS_in_createFunctionStatement4676); if (state.failed) return stmt;
			pushFollow(FOLLOW_comparatorType_in_createFunctionStatement4682);
			returnType=comparatorType();
			state._fsp--;
			if (state.failed) return stmt;
			match(input,K_LANGUAGE,FOLLOW_K_LANGUAGE_in_createFunctionStatement4690); if (state.failed) return stmt;
			language=(Token)match(input,IDENT,FOLLOW_IDENT_in_createFunctionStatement4696); if (state.failed) return stmt;
			match(input,K_AS,FOLLOW_K_AS_in_createFunctionStatement4704); if (state.failed) return stmt;
			body=(Token)match(input,STRING_LITERAL,FOLLOW_STRING_LITERAL_in_createFunctionStatement4710); if (state.failed) return stmt;
			if ( state.backtracking==0 ) { stmt = new CreateFunctionStatement.Raw(
			          fn, argNames, argTypes, returnType, calledOnNullInput, (language!=null?language.getText():null).toLowerCase(), (body!=null?body.getText():null), orReplace, ifNotExists);
			      }
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return stmt;
	}
	// $ANTLR end "createFunctionStatement"



	// $ANTLR start "dropFunctionStatement"
	// Parser.g:729:1: dropFunctionStatement returns [DropFunctionStatement.Raw stmt] : K_DROP K_FUNCTION ( K_IF K_EXISTS )? fn= functionName ( '(' (v= comparatorType ( ',' v= comparatorType )* )? ')' )? ;
	public final DropFunctionStatement.Raw dropFunctionStatement() throws RecognitionException {
		DropFunctionStatement.Raw stmt = null;


		FunctionName fn =null;
		CQL3Type.Raw v =null;


		        boolean ifExists = false;
		        List<CQL3Type.Raw> argTypes = new ArrayList<>();
		        boolean argsSpecified = false;
		    
		try {
			// Parser.g:735:5: ( K_DROP K_FUNCTION ( K_IF K_EXISTS )? fn= functionName ( '(' (v= comparatorType ( ',' v= comparatorType )* )? ')' )? )
			// Parser.g:735:7: K_DROP K_FUNCTION ( K_IF K_EXISTS )? fn= functionName ( '(' (v= comparatorType ( ',' v= comparatorType )* )? ')' )?
			{
			match(input,K_DROP,FOLLOW_K_DROP_in_dropFunctionStatement4748); if (state.failed) return stmt;
			match(input,K_FUNCTION,FOLLOW_K_FUNCTION_in_dropFunctionStatement4750); if (state.failed) return stmt;
			// Parser.g:736:7: ( K_IF K_EXISTS )?
			int alt82=2;
			int LA82_0 = input.LA(1);
			if ( (LA82_0==K_IF) ) {
				alt82=1;
			}
			switch (alt82) {
				case 1 :
					// Parser.g:736:8: K_IF K_EXISTS
					{
					match(input,K_IF,FOLLOW_K_IF_in_dropFunctionStatement4759); if (state.failed) return stmt;
					match(input,K_EXISTS,FOLLOW_K_EXISTS_in_dropFunctionStatement4761); if (state.failed) return stmt;
					if ( state.backtracking==0 ) { ifExists = true; }
					}
					break;

			}

			pushFollow(FOLLOW_functionName_in_dropFunctionStatement4776);
			fn=functionName();
			state._fsp--;
			if (state.failed) return stmt;
			// Parser.g:738:7: ( '(' (v= comparatorType ( ',' v= comparatorType )* )? ')' )?
			int alt85=2;
			int LA85_0 = input.LA(1);
			if ( (LA85_0==190) ) {
				alt85=1;
			}
			switch (alt85) {
				case 1 :
					// Parser.g:739:9: '(' (v= comparatorType ( ',' v= comparatorType )* )? ')'
					{
					match(input,190,FOLLOW_190_in_dropFunctionStatement4794); if (state.failed) return stmt;
					// Parser.g:740:11: (v= comparatorType ( ',' v= comparatorType )* )?
					int alt84=2;
					int LA84_0 = input.LA(1);
					if ( (LA84_0==IDENT||(LA84_0 >= K_AGGREGATE && LA84_0 <= K_ALL)||LA84_0==K_AS||LA84_0==K_ASCII||(LA84_0 >= K_BIGINT && LA84_0 <= K_BOOLEAN)||(LA84_0 >= K_CALLED && LA84_0 <= K_CLUSTERING)||(LA84_0 >= K_COMPACT && LA84_0 <= K_COUNTER)||LA84_0==K_CUSTOM||(LA84_0 >= K_DATE && LA84_0 <= K_DECIMAL)||(LA84_0 >= K_DISTINCT && LA84_0 <= K_DOUBLE)||LA84_0==K_DURATION||(LA84_0 >= K_EXISTS && LA84_0 <= K_FLOAT)||LA84_0==K_FROZEN||(LA84_0 >= K_FUNCTION && LA84_0 <= K_FUNCTIONS)||LA84_0==K_GROUP||(LA84_0 >= K_INET && LA84_0 <= K_INPUT)||LA84_0==K_INT||(LA84_0 >= K_JSON && LA84_0 <= K_KEYS)||(LA84_0 >= K_KEYSPACES && LA84_0 <= K_LIKE)||(LA84_0 >= K_LIST && LA84_0 <= K_MAP)||LA84_0==K_NOLOGIN||LA84_0==K_NOSUPERUSER||LA84_0==K_OPTIONS||(LA84_0 >= K_PARTITION && LA84_0 <= K_PERMISSIONS)||LA84_0==K_RETURNS||(LA84_0 >= K_ROLE && LA84_0 <= K_ROLES)||(LA84_0 >= K_SET && LA84_0 <= K_TINYINT)||LA84_0==K_TRIGGER||(LA84_0 >= K_TTL && LA84_0 <= K_TYPE)||(LA84_0 >= K_USER && LA84_0 <= K_USERS)||(LA84_0 >= K_UUID && LA84_0 <= K_VARINT)||LA84_0==K_WRITETIME||LA84_0==QUOTED_NAME||LA84_0==STRING_LITERAL) ) {
						alt84=1;
					}
					switch (alt84) {
						case 1 :
							// Parser.g:741:13: v= comparatorType ( ',' v= comparatorType )*
							{
							pushFollow(FOLLOW_comparatorType_in_dropFunctionStatement4822);
							v=comparatorType();
							state._fsp--;
							if (state.failed) return stmt;
							if ( state.backtracking==0 ) { argTypes.add(v); }
							// Parser.g:742:13: ( ',' v= comparatorType )*
							loop83:
							while (true) {
								int alt83=2;
								int LA83_0 = input.LA(1);
								if ( (LA83_0==194) ) {
									alt83=1;
								}

								switch (alt83) {
								case 1 :
									// Parser.g:742:15: ',' v= comparatorType
									{
									match(input,194,FOLLOW_194_in_dropFunctionStatement4840); if (state.failed) return stmt;
									pushFollow(FOLLOW_comparatorType_in_dropFunctionStatement4844);
									v=comparatorType();
									state._fsp--;
									if (state.failed) return stmt;
									if ( state.backtracking==0 ) { argTypes.add(v); }
									}
									break;

								default :
									break loop83;
								}
							}

							}
							break;

					}

					match(input,191,FOLLOW_191_in_dropFunctionStatement4872); if (state.failed) return stmt;
					if ( state.backtracking==0 ) { argsSpecified = true; }
					}
					break;

			}

			if ( state.backtracking==0 ) { stmt = new DropFunctionStatement.Raw(fn, argTypes, argsSpecified, ifExists); }
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return stmt;
	}
	// $ANTLR end "dropFunctionStatement"



	// $ANTLR start "createKeyspaceStatement"
	// Parser.g:753:1: createKeyspaceStatement returns [CreateKeyspaceStatement.Raw stmt] : K_CREATE K_KEYSPACE ( K_IF K_NOT K_EXISTS )? ks= keyspaceName K_WITH properties[attrs] ;
	public final CreateKeyspaceStatement.Raw createKeyspaceStatement() throws RecognitionException {
		CreateKeyspaceStatement.Raw stmt = null;


		String ks =null;


		        KeyspaceAttributes attrs = new KeyspaceAttributes();
		        boolean ifNotExists = false;
		    
		try {
			// Parser.g:758:5: ( K_CREATE K_KEYSPACE ( K_IF K_NOT K_EXISTS )? ks= keyspaceName K_WITH properties[attrs] )
			// Parser.g:758:7: K_CREATE K_KEYSPACE ( K_IF K_NOT K_EXISTS )? ks= keyspaceName K_WITH properties[attrs]
			{
			match(input,K_CREATE,FOLLOW_K_CREATE_in_createKeyspaceStatement4931); if (state.failed) return stmt;
			match(input,K_KEYSPACE,FOLLOW_K_KEYSPACE_in_createKeyspaceStatement4933); if (state.failed) return stmt;
			// Parser.g:758:27: ( K_IF K_NOT K_EXISTS )?
			int alt86=2;
			int LA86_0 = input.LA(1);
			if ( (LA86_0==K_IF) ) {
				alt86=1;
			}
			switch (alt86) {
				case 1 :
					// Parser.g:758:28: K_IF K_NOT K_EXISTS
					{
					match(input,K_IF,FOLLOW_K_IF_in_createKeyspaceStatement4936); if (state.failed) return stmt;
					match(input,K_NOT,FOLLOW_K_NOT_in_createKeyspaceStatement4938); if (state.failed) return stmt;
					match(input,K_EXISTS,FOLLOW_K_EXISTS_in_createKeyspaceStatement4940); if (state.failed) return stmt;
					if ( state.backtracking==0 ) { ifNotExists = true; }
					}
					break;

			}

			pushFollow(FOLLOW_keyspaceName_in_createKeyspaceStatement4949);
			ks=keyspaceName();
			state._fsp--;
			if (state.failed) return stmt;
			match(input,K_WITH,FOLLOW_K_WITH_in_createKeyspaceStatement4957); if (state.failed) return stmt;
			pushFollow(FOLLOW_properties_in_createKeyspaceStatement4959);
			properties(attrs);
			state._fsp--;
			if (state.failed) return stmt;
			if ( state.backtracking==0 ) { stmt = new CreateKeyspaceStatement.Raw(ks, attrs, ifNotExists); }
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return stmt;
	}
	// $ANTLR end "createKeyspaceStatement"



	// $ANTLR start "createTableStatement"
	// Parser.g:769:1: createTableStatement returns [CreateTableStatement.Raw stmt] : K_CREATE K_COLUMNFAMILY ( K_IF K_NOT K_EXISTS )? cf= columnFamilyName tableDefinition[stmt] ;
	public final CreateTableStatement.Raw createTableStatement() throws RecognitionException {
		CreateTableStatement.Raw stmt = null;


		QualifiedName cf =null;

		 boolean ifNotExists = false; 
		try {
			// Parser.g:771:5: ( K_CREATE K_COLUMNFAMILY ( K_IF K_NOT K_EXISTS )? cf= columnFamilyName tableDefinition[stmt] )
			// Parser.g:771:7: K_CREATE K_COLUMNFAMILY ( K_IF K_NOT K_EXISTS )? cf= columnFamilyName tableDefinition[stmt]
			{
			match(input,K_CREATE,FOLLOW_K_CREATE_in_createTableStatement4994); if (state.failed) return stmt;
			match(input,K_COLUMNFAMILY,FOLLOW_K_COLUMNFAMILY_in_createTableStatement4996); if (state.failed) return stmt;
			// Parser.g:771:31: ( K_IF K_NOT K_EXISTS )?
			int alt87=2;
			int LA87_0 = input.LA(1);
			if ( (LA87_0==K_IF) ) {
				alt87=1;
			}
			switch (alt87) {
				case 1 :
					// Parser.g:771:32: K_IF K_NOT K_EXISTS
					{
					match(input,K_IF,FOLLOW_K_IF_in_createTableStatement4999); if (state.failed) return stmt;
					match(input,K_NOT,FOLLOW_K_NOT_in_createTableStatement5001); if (state.failed) return stmt;
					match(input,K_EXISTS,FOLLOW_K_EXISTS_in_createTableStatement5003); if (state.failed) return stmt;
					if ( state.backtracking==0 ) { ifNotExists = true; }
					}
					break;

			}

			pushFollow(FOLLOW_columnFamilyName_in_createTableStatement5018);
			cf=columnFamilyName();
			state._fsp--;
			if (state.failed) return stmt;
			if ( state.backtracking==0 ) { stmt = new CreateTableStatement.Raw(cf, ifNotExists); }
			pushFollow(FOLLOW_tableDefinition_in_createTableStatement5028);
			tableDefinition(stmt);
			state._fsp--;
			if (state.failed) return stmt;
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return stmt;
	}
	// $ANTLR end "createTableStatement"



	// $ANTLR start "tableDefinition"
	// Parser.g:776:1: tableDefinition[CreateTableStatement.Raw stmt] : '(' tableColumns[stmt] ( ',' ( tableColumns[stmt] )? )* ')' ( K_WITH tableProperty[stmt] ( K_AND tableProperty[stmt] )* )? ;
	public final void tableDefinition(CreateTableStatement.Raw stmt) throws RecognitionException {
		try {
			// Parser.g:777:5: ( '(' tableColumns[stmt] ( ',' ( tableColumns[stmt] )? )* ')' ( K_WITH tableProperty[stmt] ( K_AND tableProperty[stmt] )* )? )
			// Parser.g:777:7: '(' tableColumns[stmt] ( ',' ( tableColumns[stmt] )? )* ')' ( K_WITH tableProperty[stmt] ( K_AND tableProperty[stmt] )* )?
			{
			match(input,190,FOLLOW_190_in_tableDefinition5047); if (state.failed) return;
			pushFollow(FOLLOW_tableColumns_in_tableDefinition5049);
			tableColumns(stmt);
			state._fsp--;
			if (state.failed) return;
			// Parser.g:777:30: ( ',' ( tableColumns[stmt] )? )*
			loop89:
			while (true) {
				int alt89=2;
				int LA89_0 = input.LA(1);
				if ( (LA89_0==194) ) {
					alt89=1;
				}

				switch (alt89) {
				case 1 :
					// Parser.g:777:32: ',' ( tableColumns[stmt] )?
					{
					match(input,194,FOLLOW_194_in_tableDefinition5054); if (state.failed) return;
					// Parser.g:777:36: ( tableColumns[stmt] )?
					int alt88=2;
					int LA88_0 = input.LA(1);
					if ( (LA88_0==IDENT||(LA88_0 >= K_AGGREGATE && LA88_0 <= K_ALL)||LA88_0==K_AS||LA88_0==K_ASCII||(LA88_0 >= K_BIGINT && LA88_0 <= K_BOOLEAN)||(LA88_0 >= K_CALLED && LA88_0 <= K_CLUSTERING)||(LA88_0 >= K_COMPACT && LA88_0 <= K_COUNTER)||LA88_0==K_CUSTOM||(LA88_0 >= K_DATE && LA88_0 <= K_DECIMAL)||(LA88_0 >= K_DISTINCT && LA88_0 <= K_DOUBLE)||LA88_0==K_DURATION||(LA88_0 >= K_EXISTS && LA88_0 <= K_FLOAT)||LA88_0==K_FROZEN||(LA88_0 >= K_FUNCTION && LA88_0 <= K_FUNCTIONS)||LA88_0==K_GROUP||(LA88_0 >= K_INET && LA88_0 <= K_INPUT)||LA88_0==K_INT||(LA88_0 >= K_JSON && LA88_0 <= K_KEYS)||(LA88_0 >= K_KEYSPACES && LA88_0 <= K_LIKE)||(LA88_0 >= K_LIST && LA88_0 <= K_MAP)||LA88_0==K_NOLOGIN||LA88_0==K_NOSUPERUSER||LA88_0==K_OPTIONS||(LA88_0 >= K_PARTITION && LA88_0 <= K_PERMISSIONS)||LA88_0==K_PRIMARY||LA88_0==K_RETURNS||(LA88_0 >= K_ROLE && LA88_0 <= K_ROLES)||(LA88_0 >= K_SFUNC && LA88_0 <= K_TINYINT)||LA88_0==K_TRIGGER||(LA88_0 >= K_TTL && LA88_0 <= K_TYPE)||(LA88_0 >= K_USER && LA88_0 <= K_USERS)||(LA88_0 >= K_UUID && LA88_0 <= K_VARINT)||LA88_0==K_WRITETIME||LA88_0==QUOTED_NAME) ) {
						alt88=1;
					}
					switch (alt88) {
						case 1 :
							// Parser.g:777:36: tableColumns[stmt]
							{
							pushFollow(FOLLOW_tableColumns_in_tableDefinition5056);
							tableColumns(stmt);
							state._fsp--;
							if (state.failed) return;
							}
							break;

					}

					}
					break;

				default :
					break loop89;
				}
			}

			match(input,191,FOLLOW_191_in_tableDefinition5063); if (state.failed) return;
			// Parser.g:778:7: ( K_WITH tableProperty[stmt] ( K_AND tableProperty[stmt] )* )?
			int alt91=2;
			int LA91_0 = input.LA(1);
			if ( (LA91_0==K_WITH) ) {
				alt91=1;
			}
			switch (alt91) {
				case 1 :
					// Parser.g:778:9: K_WITH tableProperty[stmt] ( K_AND tableProperty[stmt] )*
					{
					match(input,K_WITH,FOLLOW_K_WITH_in_tableDefinition5073); if (state.failed) return;
					pushFollow(FOLLOW_tableProperty_in_tableDefinition5075);
					tableProperty(stmt);
					state._fsp--;
					if (state.failed) return;
					// Parser.g:778:36: ( K_AND tableProperty[stmt] )*
					loop90:
					while (true) {
						int alt90=2;
						int LA90_0 = input.LA(1);
						if ( (LA90_0==K_AND) ) {
							alt90=1;
						}

						switch (alt90) {
						case 1 :
							// Parser.g:778:38: K_AND tableProperty[stmt]
							{
							match(input,K_AND,FOLLOW_K_AND_in_tableDefinition5080); if (state.failed) return;
							pushFollow(FOLLOW_tableProperty_in_tableDefinition5082);
							tableProperty(stmt);
							state._fsp--;
							if (state.failed) return;
							}
							break;

						default :
							break loop90;
						}
					}

					}
					break;

			}

			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "tableDefinition"



	// $ANTLR start "tableColumns"
	// Parser.g:781:1: tableColumns[CreateTableStatement.Raw stmt] : (k= ident v= comparatorType ( K_STATIC )? ( K_PRIMARY K_KEY )? | K_PRIMARY K_KEY '(' tablePartitionKey[stmt] ( ',' c= ident )* ')' );
	public final void tableColumns(CreateTableStatement.Raw stmt) throws RecognitionException {
		ColumnIdentifier k =null;
		CQL3Type.Raw v =null;
		ColumnIdentifier c =null;

		 boolean isStatic = false; 
		try {
			// Parser.g:783:5: (k= ident v= comparatorType ( K_STATIC )? ( K_PRIMARY K_KEY )? | K_PRIMARY K_KEY '(' tablePartitionKey[stmt] ( ',' c= ident )* ')' )
			int alt95=2;
			int LA95_0 = input.LA(1);
			if ( (LA95_0==IDENT||(LA95_0 >= K_AGGREGATE && LA95_0 <= K_ALL)||LA95_0==K_AS||LA95_0==K_ASCII||(LA95_0 >= K_BIGINT && LA95_0 <= K_BOOLEAN)||(LA95_0 >= K_CALLED && LA95_0 <= K_CLUSTERING)||(LA95_0 >= K_COMPACT && LA95_0 <= K_COUNTER)||LA95_0==K_CUSTOM||(LA95_0 >= K_DATE && LA95_0 <= K_DECIMAL)||(LA95_0 >= K_DISTINCT && LA95_0 <= K_DOUBLE)||LA95_0==K_DURATION||(LA95_0 >= K_EXISTS && LA95_0 <= K_FLOAT)||LA95_0==K_FROZEN||(LA95_0 >= K_FUNCTION && LA95_0 <= K_FUNCTIONS)||LA95_0==K_GROUP||(LA95_0 >= K_INET && LA95_0 <= K_INPUT)||LA95_0==K_INT||(LA95_0 >= K_JSON && LA95_0 <= K_KEYS)||(LA95_0 >= K_KEYSPACES && LA95_0 <= K_LIKE)||(LA95_0 >= K_LIST && LA95_0 <= K_MAP)||LA95_0==K_NOLOGIN||LA95_0==K_NOSUPERUSER||LA95_0==K_OPTIONS||(LA95_0 >= K_PARTITION && LA95_0 <= K_PERMISSIONS)||LA95_0==K_RETURNS||(LA95_0 >= K_ROLE && LA95_0 <= K_ROLES)||(LA95_0 >= K_SFUNC && LA95_0 <= K_TINYINT)||LA95_0==K_TRIGGER||(LA95_0 >= K_TTL && LA95_0 <= K_TYPE)||(LA95_0 >= K_USER && LA95_0 <= K_USERS)||(LA95_0 >= K_UUID && LA95_0 <= K_VARINT)||LA95_0==K_WRITETIME||LA95_0==QUOTED_NAME) ) {
				alt95=1;
			}
			else if ( (LA95_0==K_PRIMARY) ) {
				alt95=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return;}
				NoViableAltException nvae =
					new NoViableAltException("", 95, 0, input);
				throw nvae;
			}

			switch (alt95) {
				case 1 :
					// Parser.g:783:7: k= ident v= comparatorType ( K_STATIC )? ( K_PRIMARY K_KEY )?
					{
					pushFollow(FOLLOW_ident_in_tableColumns5117);
					k=ident();
					state._fsp--;
					if (state.failed) return;
					pushFollow(FOLLOW_comparatorType_in_tableColumns5121);
					v=comparatorType();
					state._fsp--;
					if (state.failed) return;
					// Parser.g:783:32: ( K_STATIC )?
					int alt92=2;
					int LA92_0 = input.LA(1);
					if ( (LA92_0==K_STATIC) ) {
						alt92=1;
					}
					switch (alt92) {
						case 1 :
							// Parser.g:783:33: K_STATIC
							{
							match(input,K_STATIC,FOLLOW_K_STATIC_in_tableColumns5124); if (state.failed) return;
							if ( state.backtracking==0 ) { isStatic = true; }
							}
							break;

					}

					if ( state.backtracking==0 ) { stmt.addColumn(k, v, isStatic); }
					// Parser.g:784:9: ( K_PRIMARY K_KEY )?
					int alt93=2;
					int LA93_0 = input.LA(1);
					if ( (LA93_0==K_PRIMARY) ) {
						alt93=1;
					}
					switch (alt93) {
						case 1 :
							// Parser.g:784:10: K_PRIMARY K_KEY
							{
							match(input,K_PRIMARY,FOLLOW_K_PRIMARY_in_tableColumns5141); if (state.failed) return;
							match(input,K_KEY,FOLLOW_K_KEY_in_tableColumns5143); if (state.failed) return;
							if ( state.backtracking==0 ) { stmt.setPartitionKeyColumn(k); }
							}
							break;

					}

					}
					break;
				case 2 :
					// Parser.g:785:7: K_PRIMARY K_KEY '(' tablePartitionKey[stmt] ( ',' c= ident )* ')'
					{
					match(input,K_PRIMARY,FOLLOW_K_PRIMARY_in_tableColumns5155); if (state.failed) return;
					match(input,K_KEY,FOLLOW_K_KEY_in_tableColumns5157); if (state.failed) return;
					match(input,190,FOLLOW_190_in_tableColumns5159); if (state.failed) return;
					pushFollow(FOLLOW_tablePartitionKey_in_tableColumns5161);
					tablePartitionKey(stmt);
					state._fsp--;
					if (state.failed) return;
					// Parser.g:785:51: ( ',' c= ident )*
					loop94:
					while (true) {
						int alt94=2;
						int LA94_0 = input.LA(1);
						if ( (LA94_0==194) ) {
							alt94=1;
						}

						switch (alt94) {
						case 1 :
							// Parser.g:785:52: ',' c= ident
							{
							match(input,194,FOLLOW_194_in_tableColumns5165); if (state.failed) return;
							pushFollow(FOLLOW_ident_in_tableColumns5169);
							c=ident();
							state._fsp--;
							if (state.failed) return;
							if ( state.backtracking==0 ) { stmt.markClusteringColumn(c); }
							}
							break;

						default :
							break loop94;
						}
					}

					match(input,191,FOLLOW_191_in_tableColumns5176); if (state.failed) return;
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "tableColumns"



	// $ANTLR start "tablePartitionKey"
	// Parser.g:788:1: tablePartitionKey[CreateTableStatement.Raw stmt] : (k1= ident | '(' k1= ident ( ',' kn= ident )* ')' );
	public final void tablePartitionKey(CreateTableStatement.Raw stmt) throws RecognitionException {
		ColumnIdentifier k1 =null;
		ColumnIdentifier kn =null;

		List<ColumnIdentifier> l = new ArrayList<ColumnIdentifier>();
		try {
			// Parser.g:791:5: (k1= ident | '(' k1= ident ( ',' kn= ident )* ')' )
			int alt97=2;
			int LA97_0 = input.LA(1);
			if ( (LA97_0==IDENT||(LA97_0 >= K_AGGREGATE && LA97_0 <= K_ALL)||LA97_0==K_AS||LA97_0==K_ASCII||(LA97_0 >= K_BIGINT && LA97_0 <= K_BOOLEAN)||(LA97_0 >= K_CALLED && LA97_0 <= K_CLUSTERING)||(LA97_0 >= K_COMPACT && LA97_0 <= K_COUNTER)||LA97_0==K_CUSTOM||(LA97_0 >= K_DATE && LA97_0 <= K_DECIMAL)||(LA97_0 >= K_DISTINCT && LA97_0 <= K_DOUBLE)||LA97_0==K_DURATION||(LA97_0 >= K_EXISTS && LA97_0 <= K_FLOAT)||LA97_0==K_FROZEN||(LA97_0 >= K_FUNCTION && LA97_0 <= K_FUNCTIONS)||LA97_0==K_GROUP||(LA97_0 >= K_INET && LA97_0 <= K_INPUT)||LA97_0==K_INT||(LA97_0 >= K_JSON && LA97_0 <= K_KEYS)||(LA97_0 >= K_KEYSPACES && LA97_0 <= K_LIKE)||(LA97_0 >= K_LIST && LA97_0 <= K_MAP)||LA97_0==K_NOLOGIN||LA97_0==K_NOSUPERUSER||LA97_0==K_OPTIONS||(LA97_0 >= K_PARTITION && LA97_0 <= K_PERMISSIONS)||LA97_0==K_RETURNS||(LA97_0 >= K_ROLE && LA97_0 <= K_ROLES)||(LA97_0 >= K_SFUNC && LA97_0 <= K_TINYINT)||LA97_0==K_TRIGGER||(LA97_0 >= K_TTL && LA97_0 <= K_TYPE)||(LA97_0 >= K_USER && LA97_0 <= K_USERS)||(LA97_0 >= K_UUID && LA97_0 <= K_VARINT)||LA97_0==K_WRITETIME||LA97_0==QUOTED_NAME) ) {
				alt97=1;
			}
			else if ( (LA97_0==190) ) {
				alt97=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return;}
				NoViableAltException nvae =
					new NoViableAltException("", 97, 0, input);
				throw nvae;
			}

			switch (alt97) {
				case 1 :
					// Parser.g:791:7: k1= ident
					{
					pushFollow(FOLLOW_ident_in_tablePartitionKey5213);
					k1=ident();
					state._fsp--;
					if (state.failed) return;
					if ( state.backtracking==0 ) { l.add(k1);}
					}
					break;
				case 2 :
					// Parser.g:792:7: '(' k1= ident ( ',' kn= ident )* ')'
					{
					match(input,190,FOLLOW_190_in_tablePartitionKey5223); if (state.failed) return;
					pushFollow(FOLLOW_ident_in_tablePartitionKey5227);
					k1=ident();
					state._fsp--;
					if (state.failed) return;
					if ( state.backtracking==0 ) { l.add(k1); }
					// Parser.g:792:35: ( ',' kn= ident )*
					loop96:
					while (true) {
						int alt96=2;
						int LA96_0 = input.LA(1);
						if ( (LA96_0==194) ) {
							alt96=1;
						}

						switch (alt96) {
						case 1 :
							// Parser.g:792:37: ',' kn= ident
							{
							match(input,194,FOLLOW_194_in_tablePartitionKey5233); if (state.failed) return;
							pushFollow(FOLLOW_ident_in_tablePartitionKey5237);
							kn=ident();
							state._fsp--;
							if (state.failed) return;
							if ( state.backtracking==0 ) { l.add(kn); }
							}
							break;

						default :
							break loop96;
						}
					}

					match(input,191,FOLLOW_191_in_tablePartitionKey5244); if (state.failed) return;
					}
					break;

			}
			if ( state.backtracking==0 ) { stmt.setPartitionKeyColumns(l); }
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "tablePartitionKey"



	// $ANTLR start "tableProperty"
	// Parser.g:795:1: tableProperty[CreateTableStatement.Raw stmt] : ( property[stmt.attrs] | K_COMPACT K_STORAGE | K_CLUSTERING K_ORDER K_BY '(' tableClusteringOrder[stmt] ( ',' tableClusteringOrder[stmt] )* ')' );
	public final void tableProperty(CreateTableStatement.Raw stmt) throws RecognitionException {
		try {
			// Parser.g:796:5: ( property[stmt.attrs] | K_COMPACT K_STORAGE | K_CLUSTERING K_ORDER K_BY '(' tableClusteringOrder[stmt] ( ',' tableClusteringOrder[stmt] )* ')' )
			int alt99=3;
			switch ( input.LA(1) ) {
			case IDENT:
			case K_AGGREGATE:
			case K_ALL:
			case K_AS:
			case K_ASCII:
			case K_BIGINT:
			case K_BLOB:
			case K_BOOLEAN:
			case K_CALLED:
			case K_CAST:
			case K_CONTAINS:
			case K_COUNT:
			case K_COUNTER:
			case K_CUSTOM:
			case K_DATE:
			case K_DECIMAL:
			case K_DISTINCT:
			case K_DOUBLE:
			case K_DURATION:
			case K_EXISTS:
			case K_FILTERING:
			case K_FINALFUNC:
			case K_FLOAT:
			case K_FROZEN:
			case K_FUNCTION:
			case K_FUNCTIONS:
			case K_GROUP:
			case K_INET:
			case K_INITCOND:
			case K_INPUT:
			case K_INT:
			case K_JSON:
			case K_KEY:
			case K_KEYS:
			case K_KEYSPACES:
			case K_LANGUAGE:
			case K_LIKE:
			case K_LIST:
			case K_LOGIN:
			case K_MAP:
			case K_NOLOGIN:
			case K_NOSUPERUSER:
			case K_OPTIONS:
			case K_PARTITION:
			case K_PASSWORD:
			case K_PER:
			case K_PERMISSION:
			case K_PERMISSIONS:
			case K_RETURNS:
			case K_ROLE:
			case K_ROLES:
			case K_SFUNC:
			case K_SMALLINT:
			case K_STATIC:
			case K_STORAGE:
			case K_STYPE:
			case K_SUPERUSER:
			case K_TEXT:
			case K_TIME:
			case K_TIMESTAMP:
			case K_TIMEUUID:
			case K_TINYINT:
			case K_TRIGGER:
			case K_TTL:
			case K_TUPLE:
			case K_TYPE:
			case K_USER:
			case K_USERS:
			case K_UUID:
			case K_VALUES:
			case K_VARCHAR:
			case K_VARINT:
			case K_WRITETIME:
			case QUOTED_NAME:
				{
				alt99=1;
				}
				break;
			case K_COMPACT:
				{
				int LA99_2 = input.LA(2);
				if ( (LA99_2==K_STORAGE) ) {
					alt99=2;
				}
				else if ( (LA99_2==203) ) {
					alt99=1;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 99, 2, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case K_CLUSTERING:
				{
				int LA99_3 = input.LA(2);
				if ( (LA99_3==K_ORDER) ) {
					alt99=3;
				}
				else if ( (LA99_3==203) ) {
					alt99=1;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 99, 3, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return;}
				NoViableAltException nvae =
					new NoViableAltException("", 99, 0, input);
				throw nvae;
			}
			switch (alt99) {
				case 1 :
					// Parser.g:796:7: property[stmt.attrs]
					{
					pushFollow(FOLLOW_property_in_tableProperty5262);
					property(stmt.attrs);
					state._fsp--;
					if (state.failed) return;
					}
					break;
				case 2 :
					// Parser.g:797:7: K_COMPACT K_STORAGE
					{
					match(input,K_COMPACT,FOLLOW_K_COMPACT_in_tableProperty5271); if (state.failed) return;
					match(input,K_STORAGE,FOLLOW_K_STORAGE_in_tableProperty5273); if (state.failed) return;
					if ( state.backtracking==0 ) { throw new SyntaxException("COMPACT STORAGE tables are not allowed starting with version 4.0"); }
					}
					break;
				case 3 :
					// Parser.g:798:7: K_CLUSTERING K_ORDER K_BY '(' tableClusteringOrder[stmt] ( ',' tableClusteringOrder[stmt] )* ')'
					{
					match(input,K_CLUSTERING,FOLLOW_K_CLUSTERING_in_tableProperty5283); if (state.failed) return;
					match(input,K_ORDER,FOLLOW_K_ORDER_in_tableProperty5285); if (state.failed) return;
					match(input,K_BY,FOLLOW_K_BY_in_tableProperty5287); if (state.failed) return;
					match(input,190,FOLLOW_190_in_tableProperty5289); if (state.failed) return;
					pushFollow(FOLLOW_tableClusteringOrder_in_tableProperty5291);
					tableClusteringOrder(stmt);
					state._fsp--;
					if (state.failed) return;
					// Parser.g:798:64: ( ',' tableClusteringOrder[stmt] )*
					loop98:
					while (true) {
						int alt98=2;
						int LA98_0 = input.LA(1);
						if ( (LA98_0==194) ) {
							alt98=1;
						}

						switch (alt98) {
						case 1 :
							// Parser.g:798:65: ',' tableClusteringOrder[stmt]
							{
							match(input,194,FOLLOW_194_in_tableProperty5295); if (state.failed) return;
							pushFollow(FOLLOW_tableClusteringOrder_in_tableProperty5297);
							tableClusteringOrder(stmt);
							state._fsp--;
							if (state.failed) return;
							}
							break;

						default :
							break loop98;
						}
					}

					match(input,191,FOLLOW_191_in_tableProperty5302); if (state.failed) return;
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "tableProperty"



	// $ANTLR start "tableClusteringOrder"
	// Parser.g:801:1: tableClusteringOrder[CreateTableStatement.Raw stmt] : k= ident ( K_ASC | K_DESC ) ;
	public final void tableClusteringOrder(CreateTableStatement.Raw stmt) throws RecognitionException {
		ColumnIdentifier k =null;

		 boolean ascending = true; 
		try {
			// Parser.g:803:5: (k= ident ( K_ASC | K_DESC ) )
			// Parser.g:803:7: k= ident ( K_ASC | K_DESC )
			{
			pushFollow(FOLLOW_ident_in_tableClusteringOrder5330);
			k=ident();
			state._fsp--;
			if (state.failed) return;
			// Parser.g:803:15: ( K_ASC | K_DESC )
			int alt100=2;
			int LA100_0 = input.LA(1);
			if ( (LA100_0==K_ASC) ) {
				alt100=1;
			}
			else if ( (LA100_0==K_DESC) ) {
				alt100=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return;}
				NoViableAltException nvae =
					new NoViableAltException("", 100, 0, input);
				throw nvae;
			}

			switch (alt100) {
				case 1 :
					// Parser.g:803:16: K_ASC
					{
					match(input,K_ASC,FOLLOW_K_ASC_in_tableClusteringOrder5333); if (state.failed) return;
					}
					break;
				case 2 :
					// Parser.g:803:24: K_DESC
					{
					match(input,K_DESC,FOLLOW_K_DESC_in_tableClusteringOrder5337); if (state.failed) return;
					if ( state.backtracking==0 ) { ascending = false; }
					}
					break;

			}

			if ( state.backtracking==0 ) { stmt.extendClusteringOrder(k, ascending); }
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "tableClusteringOrder"



	// $ANTLR start "createTypeStatement"
	// Parser.g:813:1: createTypeStatement returns [CreateTypeStatement.Raw stmt] : K_CREATE K_TYPE ( K_IF K_NOT K_EXISTS )? tn= userTypeName '(' typeColumns[stmt] ( ',' ( typeColumns[stmt] )? )* ')' ;
	public final CreateTypeStatement.Raw createTypeStatement() throws RecognitionException {
		CreateTypeStatement.Raw stmt = null;


		UTName tn =null;

		 boolean ifNotExists = false; 
		try {
			// Parser.g:815:5: ( K_CREATE K_TYPE ( K_IF K_NOT K_EXISTS )? tn= userTypeName '(' typeColumns[stmt] ( ',' ( typeColumns[stmt] )? )* ')' )
			// Parser.g:815:7: K_CREATE K_TYPE ( K_IF K_NOT K_EXISTS )? tn= userTypeName '(' typeColumns[stmt] ( ',' ( typeColumns[stmt] )? )* ')'
			{
			match(input,K_CREATE,FOLLOW_K_CREATE_in_createTypeStatement5375); if (state.failed) return stmt;
			match(input,K_TYPE,FOLLOW_K_TYPE_in_createTypeStatement5377); if (state.failed) return stmt;
			// Parser.g:815:23: ( K_IF K_NOT K_EXISTS )?
			int alt101=2;
			int LA101_0 = input.LA(1);
			if ( (LA101_0==K_IF) ) {
				alt101=1;
			}
			switch (alt101) {
				case 1 :
					// Parser.g:815:24: K_IF K_NOT K_EXISTS
					{
					match(input,K_IF,FOLLOW_K_IF_in_createTypeStatement5380); if (state.failed) return stmt;
					match(input,K_NOT,FOLLOW_K_NOT_in_createTypeStatement5382); if (state.failed) return stmt;
					match(input,K_EXISTS,FOLLOW_K_EXISTS_in_createTypeStatement5384); if (state.failed) return stmt;
					if ( state.backtracking==0 ) { ifNotExists = true; }
					}
					break;

			}

			pushFollow(FOLLOW_userTypeName_in_createTypeStatement5402);
			tn=userTypeName();
			state._fsp--;
			if (state.failed) return stmt;
			if ( state.backtracking==0 ) { stmt = new CreateTypeStatement.Raw(tn, ifNotExists); }
			match(input,190,FOLLOW_190_in_createTypeStatement5415); if (state.failed) return stmt;
			pushFollow(FOLLOW_typeColumns_in_createTypeStatement5417);
			typeColumns(stmt);
			state._fsp--;
			if (state.failed) return stmt;
			// Parser.g:817:32: ( ',' ( typeColumns[stmt] )? )*
			loop103:
			while (true) {
				int alt103=2;
				int LA103_0 = input.LA(1);
				if ( (LA103_0==194) ) {
					alt103=1;
				}

				switch (alt103) {
				case 1 :
					// Parser.g:817:34: ',' ( typeColumns[stmt] )?
					{
					match(input,194,FOLLOW_194_in_createTypeStatement5422); if (state.failed) return stmt;
					// Parser.g:817:38: ( typeColumns[stmt] )?
					int alt102=2;
					int LA102_0 = input.LA(1);
					if ( (LA102_0==IDENT||(LA102_0 >= K_AGGREGATE && LA102_0 <= K_ALL)||LA102_0==K_AS||LA102_0==K_ASCII||(LA102_0 >= K_BIGINT && LA102_0 <= K_BOOLEAN)||(LA102_0 >= K_CALLED && LA102_0 <= K_CLUSTERING)||(LA102_0 >= K_COMPACT && LA102_0 <= K_COUNTER)||LA102_0==K_CUSTOM||(LA102_0 >= K_DATE && LA102_0 <= K_DECIMAL)||(LA102_0 >= K_DISTINCT && LA102_0 <= K_DOUBLE)||LA102_0==K_DURATION||(LA102_0 >= K_EXISTS && LA102_0 <= K_FLOAT)||LA102_0==K_FROZEN||(LA102_0 >= K_FUNCTION && LA102_0 <= K_FUNCTIONS)||LA102_0==K_GROUP||(LA102_0 >= K_INET && LA102_0 <= K_INPUT)||LA102_0==K_INT||(LA102_0 >= K_JSON && LA102_0 <= K_KEYS)||(LA102_0 >= K_KEYSPACES && LA102_0 <= K_LIKE)||(LA102_0 >= K_LIST && LA102_0 <= K_MAP)||LA102_0==K_NOLOGIN||LA102_0==K_NOSUPERUSER||LA102_0==K_OPTIONS||(LA102_0 >= K_PARTITION && LA102_0 <= K_PERMISSIONS)||LA102_0==K_RETURNS||(LA102_0 >= K_ROLE && LA102_0 <= K_ROLES)||(LA102_0 >= K_SFUNC && LA102_0 <= K_TINYINT)||LA102_0==K_TRIGGER||(LA102_0 >= K_TTL && LA102_0 <= K_TYPE)||(LA102_0 >= K_USER && LA102_0 <= K_USERS)||(LA102_0 >= K_UUID && LA102_0 <= K_VARINT)||LA102_0==K_WRITETIME||LA102_0==QUOTED_NAME) ) {
						alt102=1;
					}
					switch (alt102) {
						case 1 :
							// Parser.g:817:38: typeColumns[stmt]
							{
							pushFollow(FOLLOW_typeColumns_in_createTypeStatement5424);
							typeColumns(stmt);
							state._fsp--;
							if (state.failed) return stmt;
							}
							break;

					}

					}
					break;

				default :
					break loop103;
				}
			}

			match(input,191,FOLLOW_191_in_createTypeStatement5431); if (state.failed) return stmt;
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return stmt;
	}
	// $ANTLR end "createTypeStatement"



	// $ANTLR start "typeColumns"
	// Parser.g:820:1: typeColumns[CreateTypeStatement.Raw stmt] : k= fident v= comparatorType ;
	public final void typeColumns(CreateTypeStatement.Raw stmt) throws RecognitionException {
		FieldIdentifier k =null;
		CQL3Type.Raw v =null;

		try {
			// Parser.g:821:5: (k= fident v= comparatorType )
			// Parser.g:821:7: k= fident v= comparatorType
			{
			pushFollow(FOLLOW_fident_in_typeColumns5451);
			k=fident();
			state._fsp--;
			if (state.failed) return;
			pushFollow(FOLLOW_comparatorType_in_typeColumns5455);
			v=comparatorType();
			state._fsp--;
			if (state.failed) return;
			if ( state.backtracking==0 ) { stmt.addField(k, v); }
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "typeColumns"



	// $ANTLR start "createIndexStatement"
	// Parser.g:828:1: createIndexStatement returns [CreateIndexStatement.Raw stmt] : K_CREATE ( K_CUSTOM )? K_INDEX ( K_IF K_NOT K_EXISTS )? ( idxName[name] )? K_ON cf= columnFamilyName '(' ( indexIdent[targets] ( ',' indexIdent[targets] )* )? ')' ( K_USING cls= STRING_LITERAL )? ( K_WITH properties[props] )? ;
	public final CreateIndexStatement.Raw createIndexStatement() throws RecognitionException {
		CreateIndexStatement.Raw stmt = null;


		Token cls=null;
		QualifiedName cf =null;


		        IndexAttributes props = new IndexAttributes();
		        boolean ifNotExists = false;
		        QualifiedName name = new QualifiedName();
		        List<IndexTarget.Raw> targets = new ArrayList<>();
		    
		try {
			// Parser.g:835:5: ( K_CREATE ( K_CUSTOM )? K_INDEX ( K_IF K_NOT K_EXISTS )? ( idxName[name] )? K_ON cf= columnFamilyName '(' ( indexIdent[targets] ( ',' indexIdent[targets] )* )? ')' ( K_USING cls= STRING_LITERAL )? ( K_WITH properties[props] )? )
			// Parser.g:835:7: K_CREATE ( K_CUSTOM )? K_INDEX ( K_IF K_NOT K_EXISTS )? ( idxName[name] )? K_ON cf= columnFamilyName '(' ( indexIdent[targets] ( ',' indexIdent[targets] )* )? ')' ( K_USING cls= STRING_LITERAL )? ( K_WITH properties[props] )?
			{
			match(input,K_CREATE,FOLLOW_K_CREATE_in_createIndexStatement5489); if (state.failed) return stmt;
			// Parser.g:835:16: ( K_CUSTOM )?
			int alt104=2;
			int LA104_0 = input.LA(1);
			if ( (LA104_0==K_CUSTOM) ) {
				alt104=1;
			}
			switch (alt104) {
				case 1 :
					// Parser.g:835:17: K_CUSTOM
					{
					match(input,K_CUSTOM,FOLLOW_K_CUSTOM_in_createIndexStatement5492); if (state.failed) return stmt;
					if ( state.backtracking==0 ) { props.isCustom = true; }
					}
					break;

			}

			match(input,K_INDEX,FOLLOW_K_INDEX_in_createIndexStatement5498); if (state.failed) return stmt;
			// Parser.g:835:63: ( K_IF K_NOT K_EXISTS )?
			int alt105=2;
			int LA105_0 = input.LA(1);
			if ( (LA105_0==K_IF) ) {
				alt105=1;
			}
			switch (alt105) {
				case 1 :
					// Parser.g:835:64: K_IF K_NOT K_EXISTS
					{
					match(input,K_IF,FOLLOW_K_IF_in_createIndexStatement5501); if (state.failed) return stmt;
					match(input,K_NOT,FOLLOW_K_NOT_in_createIndexStatement5503); if (state.failed) return stmt;
					match(input,K_EXISTS,FOLLOW_K_EXISTS_in_createIndexStatement5505); if (state.failed) return stmt;
					if ( state.backtracking==0 ) { ifNotExists = true; }
					}
					break;

			}

			// Parser.g:836:9: ( idxName[name] )?
			int alt106=2;
			int LA106_0 = input.LA(1);
			if ( (LA106_0==IDENT||(LA106_0 >= K_AGGREGATE && LA106_0 <= K_ALL)||LA106_0==K_AS||LA106_0==K_ASCII||(LA106_0 >= K_BIGINT && LA106_0 <= K_BOOLEAN)||(LA106_0 >= K_CALLED && LA106_0 <= K_CLUSTERING)||(LA106_0 >= K_COMPACT && LA106_0 <= K_COUNTER)||LA106_0==K_CUSTOM||(LA106_0 >= K_DATE && LA106_0 <= K_DECIMAL)||(LA106_0 >= K_DISTINCT && LA106_0 <= K_DOUBLE)||LA106_0==K_DURATION||(LA106_0 >= K_EXISTS && LA106_0 <= K_FLOAT)||LA106_0==K_FROZEN||(LA106_0 >= K_FUNCTION && LA106_0 <= K_FUNCTIONS)||LA106_0==K_GROUP||(LA106_0 >= K_INET && LA106_0 <= K_INPUT)||LA106_0==K_INT||(LA106_0 >= K_JSON && LA106_0 <= K_KEYS)||(LA106_0 >= K_KEYSPACES && LA106_0 <= K_LIKE)||(LA106_0 >= K_LIST && LA106_0 <= K_MAP)||LA106_0==K_NOLOGIN||LA106_0==K_NOSUPERUSER||LA106_0==K_OPTIONS||(LA106_0 >= K_PARTITION && LA106_0 <= K_PERMISSIONS)||LA106_0==K_RETURNS||(LA106_0 >= K_ROLE && LA106_0 <= K_ROLES)||(LA106_0 >= K_SFUNC && LA106_0 <= K_TINYINT)||LA106_0==K_TRIGGER||(LA106_0 >= K_TTL && LA106_0 <= K_TYPE)||(LA106_0 >= K_USER && LA106_0 <= K_USERS)||(LA106_0 >= K_UUID && LA106_0 <= K_VARINT)||LA106_0==K_WRITETIME||(LA106_0 >= QMARK && LA106_0 <= QUOTED_NAME)) ) {
				alt106=1;
			}
			switch (alt106) {
				case 1 :
					// Parser.g:836:10: idxName[name]
					{
					pushFollow(FOLLOW_idxName_in_createIndexStatement5521);
					idxName(name);
					state._fsp--;
					if (state.failed) return stmt;
					}
					break;

			}

			match(input,K_ON,FOLLOW_K_ON_in_createIndexStatement5526); if (state.failed) return stmt;
			pushFollow(FOLLOW_columnFamilyName_in_createIndexStatement5530);
			cf=columnFamilyName();
			state._fsp--;
			if (state.failed) return stmt;
			match(input,190,FOLLOW_190_in_createIndexStatement5532); if (state.failed) return stmt;
			// Parser.g:836:55: ( indexIdent[targets] ( ',' indexIdent[targets] )* )?
			int alt108=2;
			int LA108_0 = input.LA(1);
			if ( (LA108_0==EMPTY_QUOTED_NAME||LA108_0==IDENT||(LA108_0 >= K_AGGREGATE && LA108_0 <= K_ALL)||LA108_0==K_AS||LA108_0==K_ASCII||(LA108_0 >= K_BIGINT && LA108_0 <= K_BOOLEAN)||(LA108_0 >= K_CALLED && LA108_0 <= K_CLUSTERING)||(LA108_0 >= K_COMPACT && LA108_0 <= K_COUNTER)||LA108_0==K_CUSTOM||(LA108_0 >= K_DATE && LA108_0 <= K_DECIMAL)||(LA108_0 >= K_DISTINCT && LA108_0 <= K_DOUBLE)||(LA108_0 >= K_DURATION && LA108_0 <= K_ENTRIES)||(LA108_0 >= K_EXISTS && LA108_0 <= K_FLOAT)||(LA108_0 >= K_FROZEN && LA108_0 <= K_FUNCTIONS)||LA108_0==K_GROUP||(LA108_0 >= K_INET && LA108_0 <= K_INPUT)||LA108_0==K_INT||(LA108_0 >= K_JSON && LA108_0 <= K_KEYS)||(LA108_0 >= K_KEYSPACES && LA108_0 <= K_LIKE)||(LA108_0 >= K_LIST && LA108_0 <= K_MAP)||LA108_0==K_NOLOGIN||LA108_0==K_NOSUPERUSER||LA108_0==K_OPTIONS||(LA108_0 >= K_PARTITION && LA108_0 <= K_PERMISSIONS)||LA108_0==K_RETURNS||(LA108_0 >= K_ROLE && LA108_0 <= K_ROLES)||(LA108_0 >= K_SFUNC && LA108_0 <= K_TINYINT)||LA108_0==K_TRIGGER||(LA108_0 >= K_TTL && LA108_0 <= K_TYPE)||(LA108_0 >= K_USER && LA108_0 <= K_USERS)||(LA108_0 >= K_UUID && LA108_0 <= K_VARINT)||LA108_0==K_WRITETIME||LA108_0==QUOTED_NAME) ) {
				alt108=1;
			}
			switch (alt108) {
				case 1 :
					// Parser.g:836:56: indexIdent[targets] ( ',' indexIdent[targets] )*
					{
					pushFollow(FOLLOW_indexIdent_in_createIndexStatement5535);
					indexIdent(targets);
					state._fsp--;
					if (state.failed) return stmt;
					// Parser.g:836:76: ( ',' indexIdent[targets] )*
					loop107:
					while (true) {
						int alt107=2;
						int LA107_0 = input.LA(1);
						if ( (LA107_0==194) ) {
							alt107=1;
						}

						switch (alt107) {
						case 1 :
							// Parser.g:836:77: ',' indexIdent[targets]
							{
							match(input,194,FOLLOW_194_in_createIndexStatement5539); if (state.failed) return stmt;
							pushFollow(FOLLOW_indexIdent_in_createIndexStatement5541);
							indexIdent(targets);
							state._fsp--;
							if (state.failed) return stmt;
							}
							break;

						default :
							break loop107;
						}
					}

					}
					break;

			}

			match(input,191,FOLLOW_191_in_createIndexStatement5548); if (state.failed) return stmt;
			// Parser.g:837:9: ( K_USING cls= STRING_LITERAL )?
			int alt109=2;
			int LA109_0 = input.LA(1);
			if ( (LA109_0==K_USING) ) {
				alt109=1;
			}
			switch (alt109) {
				case 1 :
					// Parser.g:837:10: K_USING cls= STRING_LITERAL
					{
					match(input,K_USING,FOLLOW_K_USING_in_createIndexStatement5559); if (state.failed) return stmt;
					cls=(Token)match(input,STRING_LITERAL,FOLLOW_STRING_LITERAL_in_createIndexStatement5563); if (state.failed) return stmt;
					if ( state.backtracking==0 ) { props.customClass = (cls!=null?cls.getText():null); }
					}
					break;

			}

			// Parser.g:838:9: ( K_WITH properties[props] )?
			int alt110=2;
			int LA110_0 = input.LA(1);
			if ( (LA110_0==K_WITH) ) {
				alt110=1;
			}
			switch (alt110) {
				case 1 :
					// Parser.g:838:10: K_WITH properties[props]
					{
					match(input,K_WITH,FOLLOW_K_WITH_in_createIndexStatement5578); if (state.failed) return stmt;
					pushFollow(FOLLOW_properties_in_createIndexStatement5580);
					properties(props);
					state._fsp--;
					if (state.failed) return stmt;
					}
					break;

			}

			if ( state.backtracking==0 ) { stmt = new CreateIndexStatement.Raw(cf, name, targets, props, ifNotExists); }
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return stmt;
	}
	// $ANTLR end "createIndexStatement"



	// $ANTLR start "indexIdent"
	// Parser.g:842:1: indexIdent[List<IndexTarget.Raw> targets] : (c= cident | K_VALUES '(' c= cident ')' | K_KEYS '(' c= cident ')' | K_ENTRIES '(' c= cident ')' | K_FULL '(' c= cident ')' );
	public final void indexIdent(List<IndexTarget.Raw> targets) throws RecognitionException {
		ColumnMetadata.Raw c =null;

		try {
			// Parser.g:843:5: (c= cident | K_VALUES '(' c= cident ')' | K_KEYS '(' c= cident ')' | K_ENTRIES '(' c= cident ')' | K_FULL '(' c= cident ')' )
			int alt111=5;
			switch ( input.LA(1) ) {
			case EMPTY_QUOTED_NAME:
			case IDENT:
			case K_AGGREGATE:
			case K_ALL:
			case K_AS:
			case K_ASCII:
			case K_BIGINT:
			case K_BLOB:
			case K_BOOLEAN:
			case K_CALLED:
			case K_CAST:
			case K_CLUSTERING:
			case K_COMPACT:
			case K_CONTAINS:
			case K_COUNT:
			case K_COUNTER:
			case K_CUSTOM:
			case K_DATE:
			case K_DECIMAL:
			case K_DISTINCT:
			case K_DOUBLE:
			case K_DURATION:
			case K_EXISTS:
			case K_FILTERING:
			case K_FINALFUNC:
			case K_FLOAT:
			case K_FROZEN:
			case K_FUNCTION:
			case K_FUNCTIONS:
			case K_GROUP:
			case K_INET:
			case K_INITCOND:
			case K_INPUT:
			case K_INT:
			case K_JSON:
			case K_KEY:
			case K_KEYSPACES:
			case K_LANGUAGE:
			case K_LIKE:
			case K_LIST:
			case K_LOGIN:
			case K_MAP:
			case K_NOLOGIN:
			case K_NOSUPERUSER:
			case K_OPTIONS:
			case K_PARTITION:
			case K_PASSWORD:
			case K_PER:
			case K_PERMISSION:
			case K_PERMISSIONS:
			case K_RETURNS:
			case K_ROLE:
			case K_ROLES:
			case K_SFUNC:
			case K_SMALLINT:
			case K_STATIC:
			case K_STORAGE:
			case K_STYPE:
			case K_SUPERUSER:
			case K_TEXT:
			case K_TIME:
			case K_TIMESTAMP:
			case K_TIMEUUID:
			case K_TINYINT:
			case K_TRIGGER:
			case K_TTL:
			case K_TUPLE:
			case K_TYPE:
			case K_USER:
			case K_USERS:
			case K_UUID:
			case K_VARCHAR:
			case K_VARINT:
			case K_WRITETIME:
			case QUOTED_NAME:
				{
				alt111=1;
				}
				break;
			case K_VALUES:
				{
				int LA111_2 = input.LA(2);
				if ( (LA111_2==190) ) {
					alt111=2;
				}
				else if ( (LA111_2==191||LA111_2==194) ) {
					alt111=1;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 111, 2, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case K_KEYS:
				{
				int LA111_3 = input.LA(2);
				if ( (LA111_3==190) ) {
					alt111=3;
				}
				else if ( (LA111_3==191||LA111_3==194) ) {
					alt111=1;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 111, 3, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case K_ENTRIES:
				{
				alt111=4;
				}
				break;
			case K_FULL:
				{
				alt111=5;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return;}
				NoViableAltException nvae =
					new NoViableAltException("", 111, 0, input);
				throw nvae;
			}
			switch (alt111) {
				case 1 :
					// Parser.g:843:7: c= cident
					{
					pushFollow(FOLLOW_cident_in_indexIdent5612);
					c=cident();
					state._fsp--;
					if (state.failed) return;
					if ( state.backtracking==0 ) { targets.add(IndexTarget.Raw.simpleIndexOn(c)); }
					}
					break;
				case 2 :
					// Parser.g:844:7: K_VALUES '(' c= cident ')'
					{
					match(input,K_VALUES,FOLLOW_K_VALUES_in_indexIdent5640); if (state.failed) return;
					match(input,190,FOLLOW_190_in_indexIdent5642); if (state.failed) return;
					pushFollow(FOLLOW_cident_in_indexIdent5646);
					c=cident();
					state._fsp--;
					if (state.failed) return;
					match(input,191,FOLLOW_191_in_indexIdent5648); if (state.failed) return;
					if ( state.backtracking==0 ) { targets.add(IndexTarget.Raw.valuesOf(c)); }
					}
					break;
				case 3 :
					// Parser.g:845:7: K_KEYS '(' c= cident ')'
					{
					match(input,K_KEYS,FOLLOW_K_KEYS_in_indexIdent5659); if (state.failed) return;
					match(input,190,FOLLOW_190_in_indexIdent5661); if (state.failed) return;
					pushFollow(FOLLOW_cident_in_indexIdent5665);
					c=cident();
					state._fsp--;
					if (state.failed) return;
					match(input,191,FOLLOW_191_in_indexIdent5667); if (state.failed) return;
					if ( state.backtracking==0 ) { targets.add(IndexTarget.Raw.keysOf(c)); }
					}
					break;
				case 4 :
					// Parser.g:846:7: K_ENTRIES '(' c= cident ')'
					{
					match(input,K_ENTRIES,FOLLOW_K_ENTRIES_in_indexIdent5680); if (state.failed) return;
					match(input,190,FOLLOW_190_in_indexIdent5682); if (state.failed) return;
					pushFollow(FOLLOW_cident_in_indexIdent5686);
					c=cident();
					state._fsp--;
					if (state.failed) return;
					match(input,191,FOLLOW_191_in_indexIdent5688); if (state.failed) return;
					if ( state.backtracking==0 ) { targets.add(IndexTarget.Raw.keysAndValuesOf(c)); }
					}
					break;
				case 5 :
					// Parser.g:847:7: K_FULL '(' c= cident ')'
					{
					match(input,K_FULL,FOLLOW_K_FULL_in_indexIdent5698); if (state.failed) return;
					match(input,190,FOLLOW_190_in_indexIdent5700); if (state.failed) return;
					pushFollow(FOLLOW_cident_in_indexIdent5704);
					c=cident();
					state._fsp--;
					if (state.failed) return;
					match(input,191,FOLLOW_191_in_indexIdent5706); if (state.failed) return;
					if ( state.backtracking==0 ) { targets.add(IndexTarget.Raw.fullCollection(c)); }
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "indexIdent"



	// $ANTLR start "createMaterializedViewStatement"
	// Parser.g:858:1: createMaterializedViewStatement returns [CreateViewStatement.Raw stmt] : K_CREATE K_MATERIALIZED K_VIEW ( K_IF K_NOT K_EXISTS )? cf= columnFamilyName K_AS K_SELECT sclause= selectors K_FROM basecf= columnFamilyName ( K_WHERE wclause= whereClause )? viewPrimaryKey[stmt] ( K_WITH viewProperty[stmt] ( K_AND viewProperty[stmt] )* )? ;
	public final CreateViewStatement.Raw createMaterializedViewStatement() throws RecognitionException {
		CreateViewStatement.Raw stmt = null;


		QualifiedName cf =null;
		List<RawSelector> sclause =null;
		QualifiedName basecf =null;
		WhereClause.Builder wclause =null;


		        boolean ifNotExists = false;
		    
		try {
			// Parser.g:862:5: ( K_CREATE K_MATERIALIZED K_VIEW ( K_IF K_NOT K_EXISTS )? cf= columnFamilyName K_AS K_SELECT sclause= selectors K_FROM basecf= columnFamilyName ( K_WHERE wclause= whereClause )? viewPrimaryKey[stmt] ( K_WITH viewProperty[stmt] ( K_AND viewProperty[stmt] )* )? )
			// Parser.g:862:7: K_CREATE K_MATERIALIZED K_VIEW ( K_IF K_NOT K_EXISTS )? cf= columnFamilyName K_AS K_SELECT sclause= selectors K_FROM basecf= columnFamilyName ( K_WHERE wclause= whereClause )? viewPrimaryKey[stmt] ( K_WITH viewProperty[stmt] ( K_AND viewProperty[stmt] )* )?
			{
			match(input,K_CREATE,FOLLOW_K_CREATE_in_createMaterializedViewStatement5743); if (state.failed) return stmt;
			match(input,K_MATERIALIZED,FOLLOW_K_MATERIALIZED_in_createMaterializedViewStatement5745); if (state.failed) return stmt;
			match(input,K_VIEW,FOLLOW_K_VIEW_in_createMaterializedViewStatement5747); if (state.failed) return stmt;
			// Parser.g:862:38: ( K_IF K_NOT K_EXISTS )?
			int alt112=2;
			int LA112_0 = input.LA(1);
			if ( (LA112_0==K_IF) ) {
				alt112=1;
			}
			switch (alt112) {
				case 1 :
					// Parser.g:862:39: K_IF K_NOT K_EXISTS
					{
					match(input,K_IF,FOLLOW_K_IF_in_createMaterializedViewStatement5750); if (state.failed) return stmt;
					match(input,K_NOT,FOLLOW_K_NOT_in_createMaterializedViewStatement5752); if (state.failed) return stmt;
					match(input,K_EXISTS,FOLLOW_K_EXISTS_in_createMaterializedViewStatement5754); if (state.failed) return stmt;
					if ( state.backtracking==0 ) { ifNotExists = true; }
					}
					break;

			}

			pushFollow(FOLLOW_columnFamilyName_in_createMaterializedViewStatement5762);
			cf=columnFamilyName();
			state._fsp--;
			if (state.failed) return stmt;
			match(input,K_AS,FOLLOW_K_AS_in_createMaterializedViewStatement5764); if (state.failed) return stmt;
			match(input,K_SELECT,FOLLOW_K_SELECT_in_createMaterializedViewStatement5774); if (state.failed) return stmt;
			pushFollow(FOLLOW_selectors_in_createMaterializedViewStatement5778);
			sclause=selectors();
			state._fsp--;
			if (state.failed) return stmt;
			match(input,K_FROM,FOLLOW_K_FROM_in_createMaterializedViewStatement5780); if (state.failed) return stmt;
			pushFollow(FOLLOW_columnFamilyName_in_createMaterializedViewStatement5784);
			basecf=columnFamilyName();
			state._fsp--;
			if (state.failed) return stmt;
			// Parser.g:864:9: ( K_WHERE wclause= whereClause )?
			int alt113=2;
			int LA113_0 = input.LA(1);
			if ( (LA113_0==K_WHERE) ) {
				alt113=1;
			}
			switch (alt113) {
				case 1 :
					// Parser.g:864:10: K_WHERE wclause= whereClause
					{
					match(input,K_WHERE,FOLLOW_K_WHERE_in_createMaterializedViewStatement5795); if (state.failed) return stmt;
					pushFollow(FOLLOW_whereClause_in_createMaterializedViewStatement5799);
					wclause=whereClause();
					state._fsp--;
					if (state.failed) return stmt;
					}
					break;

			}

			if ( state.backtracking==0 ) {
			             WhereClause where = wclause == null ? WhereClause.empty() : wclause.build();
			             stmt = new CreateViewStatement.Raw(basecf, cf, sclause, where, ifNotExists);
			        }
			pushFollow(FOLLOW_viewPrimaryKey_in_createMaterializedViewStatement5821);
			viewPrimaryKey(stmt);
			state._fsp--;
			if (state.failed) return stmt;
			// Parser.g:870:9: ( K_WITH viewProperty[stmt] ( K_AND viewProperty[stmt] )* )?
			int alt115=2;
			int LA115_0 = input.LA(1);
			if ( (LA115_0==K_WITH) ) {
				alt115=1;
			}
			switch (alt115) {
				case 1 :
					// Parser.g:870:11: K_WITH viewProperty[stmt] ( K_AND viewProperty[stmt] )*
					{
					match(input,K_WITH,FOLLOW_K_WITH_in_createMaterializedViewStatement5834); if (state.failed) return stmt;
					pushFollow(FOLLOW_viewProperty_in_createMaterializedViewStatement5836);
					viewProperty(stmt);
					state._fsp--;
					if (state.failed) return stmt;
					// Parser.g:870:37: ( K_AND viewProperty[stmt] )*
					loop114:
					while (true) {
						int alt114=2;
						int LA114_0 = input.LA(1);
						if ( (LA114_0==K_AND) ) {
							alt114=1;
						}

						switch (alt114) {
						case 1 :
							// Parser.g:870:39: K_AND viewProperty[stmt]
							{
							match(input,K_AND,FOLLOW_K_AND_in_createMaterializedViewStatement5841); if (state.failed) return stmt;
							pushFollow(FOLLOW_viewProperty_in_createMaterializedViewStatement5843);
							viewProperty(stmt);
							state._fsp--;
							if (state.failed) return stmt;
							}
							break;

						default :
							break loop114;
						}
					}

					}
					break;

			}

			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return stmt;
	}
	// $ANTLR end "createMaterializedViewStatement"



	// $ANTLR start "viewPrimaryKey"
	// Parser.g:873:1: viewPrimaryKey[CreateViewStatement.Raw stmt] : K_PRIMARY K_KEY '(' viewPartitionKey[stmt] ( ',' c= ident )* ')' ;
	public final void viewPrimaryKey(CreateViewStatement.Raw stmt) throws RecognitionException {
		ColumnIdentifier c =null;

		try {
			// Parser.g:874:5: ( K_PRIMARY K_KEY '(' viewPartitionKey[stmt] ( ',' c= ident )* ')' )
			// Parser.g:874:7: K_PRIMARY K_KEY '(' viewPartitionKey[stmt] ( ',' c= ident )* ')'
			{
			match(input,K_PRIMARY,FOLLOW_K_PRIMARY_in_viewPrimaryKey5867); if (state.failed) return;
			match(input,K_KEY,FOLLOW_K_KEY_in_viewPrimaryKey5869); if (state.failed) return;
			match(input,190,FOLLOW_190_in_viewPrimaryKey5871); if (state.failed) return;
			pushFollow(FOLLOW_viewPartitionKey_in_viewPrimaryKey5873);
			viewPartitionKey(stmt);
			state._fsp--;
			if (state.failed) return;
			// Parser.g:874:50: ( ',' c= ident )*
			loop116:
			while (true) {
				int alt116=2;
				int LA116_0 = input.LA(1);
				if ( (LA116_0==194) ) {
					alt116=1;
				}

				switch (alt116) {
				case 1 :
					// Parser.g:874:51: ',' c= ident
					{
					match(input,194,FOLLOW_194_in_viewPrimaryKey5877); if (state.failed) return;
					pushFollow(FOLLOW_ident_in_viewPrimaryKey5881);
					c=ident();
					state._fsp--;
					if (state.failed) return;
					if ( state.backtracking==0 ) { stmt.markClusteringColumn(c); }
					}
					break;

				default :
					break loop116;
				}
			}

			match(input,191,FOLLOW_191_in_viewPrimaryKey5888); if (state.failed) return;
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "viewPrimaryKey"



	// $ANTLR start "viewPartitionKey"
	// Parser.g:877:1: viewPartitionKey[CreateViewStatement.Raw stmt] : (k1= ident | '(' k1= ident ( ',' kn= ident )* ')' );
	public final void viewPartitionKey(CreateViewStatement.Raw stmt) throws RecognitionException {
		ColumnIdentifier k1 =null;
		ColumnIdentifier kn =null;

		List<ColumnIdentifier> l = new ArrayList<ColumnIdentifier>();
		try {
			// Parser.g:880:5: (k1= ident | '(' k1= ident ( ',' kn= ident )* ')' )
			int alt118=2;
			int LA118_0 = input.LA(1);
			if ( (LA118_0==IDENT||(LA118_0 >= K_AGGREGATE && LA118_0 <= K_ALL)||LA118_0==K_AS||LA118_0==K_ASCII||(LA118_0 >= K_BIGINT && LA118_0 <= K_BOOLEAN)||(LA118_0 >= K_CALLED && LA118_0 <= K_CLUSTERING)||(LA118_0 >= K_COMPACT && LA118_0 <= K_COUNTER)||LA118_0==K_CUSTOM||(LA118_0 >= K_DATE && LA118_0 <= K_DECIMAL)||(LA118_0 >= K_DISTINCT && LA118_0 <= K_DOUBLE)||LA118_0==K_DURATION||(LA118_0 >= K_EXISTS && LA118_0 <= K_FLOAT)||LA118_0==K_FROZEN||(LA118_0 >= K_FUNCTION && LA118_0 <= K_FUNCTIONS)||LA118_0==K_GROUP||(LA118_0 >= K_INET && LA118_0 <= K_INPUT)||LA118_0==K_INT||(LA118_0 >= K_JSON && LA118_0 <= K_KEYS)||(LA118_0 >= K_KEYSPACES && LA118_0 <= K_LIKE)||(LA118_0 >= K_LIST && LA118_0 <= K_MAP)||LA118_0==K_NOLOGIN||LA118_0==K_NOSUPERUSER||LA118_0==K_OPTIONS||(LA118_0 >= K_PARTITION && LA118_0 <= K_PERMISSIONS)||LA118_0==K_RETURNS||(LA118_0 >= K_ROLE && LA118_0 <= K_ROLES)||(LA118_0 >= K_SFUNC && LA118_0 <= K_TINYINT)||LA118_0==K_TRIGGER||(LA118_0 >= K_TTL && LA118_0 <= K_TYPE)||(LA118_0 >= K_USER && LA118_0 <= K_USERS)||(LA118_0 >= K_UUID && LA118_0 <= K_VARINT)||LA118_0==K_WRITETIME||LA118_0==QUOTED_NAME) ) {
				alt118=1;
			}
			else if ( (LA118_0==190) ) {
				alt118=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return;}
				NoViableAltException nvae =
					new NoViableAltException("", 118, 0, input);
				throw nvae;
			}

			switch (alt118) {
				case 1 :
					// Parser.g:880:7: k1= ident
					{
					pushFollow(FOLLOW_ident_in_viewPartitionKey5925);
					k1=ident();
					state._fsp--;
					if (state.failed) return;
					if ( state.backtracking==0 ) { l.add(k1);}
					}
					break;
				case 2 :
					// Parser.g:881:7: '(' k1= ident ( ',' kn= ident )* ')'
					{
					match(input,190,FOLLOW_190_in_viewPartitionKey5935); if (state.failed) return;
					pushFollow(FOLLOW_ident_in_viewPartitionKey5939);
					k1=ident();
					state._fsp--;
					if (state.failed) return;
					if ( state.backtracking==0 ) { l.add(k1); }
					// Parser.g:881:35: ( ',' kn= ident )*
					loop117:
					while (true) {
						int alt117=2;
						int LA117_0 = input.LA(1);
						if ( (LA117_0==194) ) {
							alt117=1;
						}

						switch (alt117) {
						case 1 :
							// Parser.g:881:37: ',' kn= ident
							{
							match(input,194,FOLLOW_194_in_viewPartitionKey5945); if (state.failed) return;
							pushFollow(FOLLOW_ident_in_viewPartitionKey5949);
							kn=ident();
							state._fsp--;
							if (state.failed) return;
							if ( state.backtracking==0 ) { l.add(kn); }
							}
							break;

						default :
							break loop117;
						}
					}

					match(input,191,FOLLOW_191_in_viewPartitionKey5956); if (state.failed) return;
					}
					break;

			}
			if ( state.backtracking==0 ) { stmt.setPartitionKeyColumns(l); }
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "viewPartitionKey"



	// $ANTLR start "viewProperty"
	// Parser.g:884:1: viewProperty[CreateViewStatement.Raw stmt] : ( property[stmt.attrs] | K_COMPACT K_STORAGE | K_CLUSTERING K_ORDER K_BY '(' viewClusteringOrder[stmt] ( ',' viewClusteringOrder[stmt] )* ')' );
	public final void viewProperty(CreateViewStatement.Raw stmt) throws RecognitionException {
		try {
			// Parser.g:885:5: ( property[stmt.attrs] | K_COMPACT K_STORAGE | K_CLUSTERING K_ORDER K_BY '(' viewClusteringOrder[stmt] ( ',' viewClusteringOrder[stmt] )* ')' )
			int alt120=3;
			switch ( input.LA(1) ) {
			case IDENT:
			case K_AGGREGATE:
			case K_ALL:
			case K_AS:
			case K_ASCII:
			case K_BIGINT:
			case K_BLOB:
			case K_BOOLEAN:
			case K_CALLED:
			case K_CAST:
			case K_CONTAINS:
			case K_COUNT:
			case K_COUNTER:
			case K_CUSTOM:
			case K_DATE:
			case K_DECIMAL:
			case K_DISTINCT:
			case K_DOUBLE:
			case K_DURATION:
			case K_EXISTS:
			case K_FILTERING:
			case K_FINALFUNC:
			case K_FLOAT:
			case K_FROZEN:
			case K_FUNCTION:
			case K_FUNCTIONS:
			case K_GROUP:
			case K_INET:
			case K_INITCOND:
			case K_INPUT:
			case K_INT:
			case K_JSON:
			case K_KEY:
			case K_KEYS:
			case K_KEYSPACES:
			case K_LANGUAGE:
			case K_LIKE:
			case K_LIST:
			case K_LOGIN:
			case K_MAP:
			case K_NOLOGIN:
			case K_NOSUPERUSER:
			case K_OPTIONS:
			case K_PARTITION:
			case K_PASSWORD:
			case K_PER:
			case K_PERMISSION:
			case K_PERMISSIONS:
			case K_RETURNS:
			case K_ROLE:
			case K_ROLES:
			case K_SFUNC:
			case K_SMALLINT:
			case K_STATIC:
			case K_STORAGE:
			case K_STYPE:
			case K_SUPERUSER:
			case K_TEXT:
			case K_TIME:
			case K_TIMESTAMP:
			case K_TIMEUUID:
			case K_TINYINT:
			case K_TRIGGER:
			case K_TTL:
			case K_TUPLE:
			case K_TYPE:
			case K_USER:
			case K_USERS:
			case K_UUID:
			case K_VALUES:
			case K_VARCHAR:
			case K_VARINT:
			case K_WRITETIME:
			case QUOTED_NAME:
				{
				alt120=1;
				}
				break;
			case K_COMPACT:
				{
				int LA120_2 = input.LA(2);
				if ( (LA120_2==K_STORAGE) ) {
					alt120=2;
				}
				else if ( (LA120_2==203) ) {
					alt120=1;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 120, 2, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case K_CLUSTERING:
				{
				int LA120_3 = input.LA(2);
				if ( (LA120_3==K_ORDER) ) {
					alt120=3;
				}
				else if ( (LA120_3==203) ) {
					alt120=1;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 120, 3, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return;}
				NoViableAltException nvae =
					new NoViableAltException("", 120, 0, input);
				throw nvae;
			}
			switch (alt120) {
				case 1 :
					// Parser.g:885:7: property[stmt.attrs]
					{
					pushFollow(FOLLOW_property_in_viewProperty5974);
					property(stmt.attrs);
					state._fsp--;
					if (state.failed) return;
					}
					break;
				case 2 :
					// Parser.g:886:7: K_COMPACT K_STORAGE
					{
					match(input,K_COMPACT,FOLLOW_K_COMPACT_in_viewProperty5983); if (state.failed) return;
					match(input,K_STORAGE,FOLLOW_K_STORAGE_in_viewProperty5985); if (state.failed) return;
					if ( state.backtracking==0 ) { throw new SyntaxException("COMPACT STORAGE tables are not allowed starting with version 4.0"); }
					}
					break;
				case 3 :
					// Parser.g:887:7: K_CLUSTERING K_ORDER K_BY '(' viewClusteringOrder[stmt] ( ',' viewClusteringOrder[stmt] )* ')'
					{
					match(input,K_CLUSTERING,FOLLOW_K_CLUSTERING_in_viewProperty5995); if (state.failed) return;
					match(input,K_ORDER,FOLLOW_K_ORDER_in_viewProperty5997); if (state.failed) return;
					match(input,K_BY,FOLLOW_K_BY_in_viewProperty5999); if (state.failed) return;
					match(input,190,FOLLOW_190_in_viewProperty6001); if (state.failed) return;
					pushFollow(FOLLOW_viewClusteringOrder_in_viewProperty6003);
					viewClusteringOrder(stmt);
					state._fsp--;
					if (state.failed) return;
					// Parser.g:887:63: ( ',' viewClusteringOrder[stmt] )*
					loop119:
					while (true) {
						int alt119=2;
						int LA119_0 = input.LA(1);
						if ( (LA119_0==194) ) {
							alt119=1;
						}

						switch (alt119) {
						case 1 :
							// Parser.g:887:64: ',' viewClusteringOrder[stmt]
							{
							match(input,194,FOLLOW_194_in_viewProperty6007); if (state.failed) return;
							pushFollow(FOLLOW_viewClusteringOrder_in_viewProperty6009);
							viewClusteringOrder(stmt);
							state._fsp--;
							if (state.failed) return;
							}
							break;

						default :
							break loop119;
						}
					}

					match(input,191,FOLLOW_191_in_viewProperty6014); if (state.failed) return;
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "viewProperty"



	// $ANTLR start "viewClusteringOrder"
	// Parser.g:890:1: viewClusteringOrder[CreateViewStatement.Raw stmt] : k= ident ( K_ASC | K_DESC ) ;
	public final void viewClusteringOrder(CreateViewStatement.Raw stmt) throws RecognitionException {
		ColumnIdentifier k =null;

		 boolean ascending = true; 
		try {
			// Parser.g:892:5: (k= ident ( K_ASC | K_DESC ) )
			// Parser.g:892:7: k= ident ( K_ASC | K_DESC )
			{
			pushFollow(FOLLOW_ident_in_viewClusteringOrder6042);
			k=ident();
			state._fsp--;
			if (state.failed) return;
			// Parser.g:892:15: ( K_ASC | K_DESC )
			int alt121=2;
			int LA121_0 = input.LA(1);
			if ( (LA121_0==K_ASC) ) {
				alt121=1;
			}
			else if ( (LA121_0==K_DESC) ) {
				alt121=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return;}
				NoViableAltException nvae =
					new NoViableAltException("", 121, 0, input);
				throw nvae;
			}

			switch (alt121) {
				case 1 :
					// Parser.g:892:16: K_ASC
					{
					match(input,K_ASC,FOLLOW_K_ASC_in_viewClusteringOrder6045); if (state.failed) return;
					}
					break;
				case 2 :
					// Parser.g:892:24: K_DESC
					{
					match(input,K_DESC,FOLLOW_K_DESC_in_viewClusteringOrder6049); if (state.failed) return;
					if ( state.backtracking==0 ) { ascending = false; }
					}
					break;

			}

			if ( state.backtracking==0 ) { stmt.extendClusteringOrder(k, ascending); }
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "viewClusteringOrder"



	// $ANTLR start "createTriggerStatement"
	// Parser.g:898:1: createTriggerStatement returns [CreateTriggerStatement.Raw stmt] : K_CREATE K_TRIGGER ( K_IF K_NOT K_EXISTS )? (name= ident ) K_ON cf= columnFamilyName K_USING cls= STRING_LITERAL ;
	public final CreateTriggerStatement.Raw createTriggerStatement() throws RecognitionException {
		CreateTriggerStatement.Raw stmt = null;


		Token cls=null;
		ColumnIdentifier name =null;
		QualifiedName cf =null;


		        boolean ifNotExists = false;
		    
		try {
			// Parser.g:902:5: ( K_CREATE K_TRIGGER ( K_IF K_NOT K_EXISTS )? (name= ident ) K_ON cf= columnFamilyName K_USING cls= STRING_LITERAL )
			// Parser.g:902:7: K_CREATE K_TRIGGER ( K_IF K_NOT K_EXISTS )? (name= ident ) K_ON cf= columnFamilyName K_USING cls= STRING_LITERAL
			{
			match(input,K_CREATE,FOLLOW_K_CREATE_in_createTriggerStatement6087); if (state.failed) return stmt;
			match(input,K_TRIGGER,FOLLOW_K_TRIGGER_in_createTriggerStatement6089); if (state.failed) return stmt;
			// Parser.g:902:26: ( K_IF K_NOT K_EXISTS )?
			int alt122=2;
			int LA122_0 = input.LA(1);
			if ( (LA122_0==K_IF) ) {
				alt122=1;
			}
			switch (alt122) {
				case 1 :
					// Parser.g:902:27: K_IF K_NOT K_EXISTS
					{
					match(input,K_IF,FOLLOW_K_IF_in_createTriggerStatement6092); if (state.failed) return stmt;
					match(input,K_NOT,FOLLOW_K_NOT_in_createTriggerStatement6094); if (state.failed) return stmt;
					match(input,K_EXISTS,FOLLOW_K_EXISTS_in_createTriggerStatement6096); if (state.failed) return stmt;
					if ( state.backtracking==0 ) { ifNotExists = true; }
					}
					break;

			}

			// Parser.g:902:74: (name= ident )
			// Parser.g:902:75: name= ident
			{
			pushFollow(FOLLOW_ident_in_createTriggerStatement6106);
			name=ident();
			state._fsp--;
			if (state.failed) return stmt;
			}

			match(input,K_ON,FOLLOW_K_ON_in_createTriggerStatement6117); if (state.failed) return stmt;
			pushFollow(FOLLOW_columnFamilyName_in_createTriggerStatement6121);
			cf=columnFamilyName();
			state._fsp--;
			if (state.failed) return stmt;
			match(input,K_USING,FOLLOW_K_USING_in_createTriggerStatement6123); if (state.failed) return stmt;
			cls=(Token)match(input,STRING_LITERAL,FOLLOW_STRING_LITERAL_in_createTriggerStatement6127); if (state.failed) return stmt;
			if ( state.backtracking==0 ) { stmt = new CreateTriggerStatement.Raw(cf, name.toString(), (cls!=null?cls.getText():null), ifNotExists); }
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return stmt;
	}
	// $ANTLR end "createTriggerStatement"



	// $ANTLR start "dropTriggerStatement"
	// Parser.g:910:1: dropTriggerStatement returns [DropTriggerStatement.Raw stmt] : K_DROP K_TRIGGER ( K_IF K_EXISTS )? (name= ident ) K_ON cf= columnFamilyName ;
	public final DropTriggerStatement.Raw dropTriggerStatement() throws RecognitionException {
		DropTriggerStatement.Raw stmt = null;


		ColumnIdentifier name =null;
		QualifiedName cf =null;

		 boolean ifExists = false; 
		try {
			// Parser.g:912:5: ( K_DROP K_TRIGGER ( K_IF K_EXISTS )? (name= ident ) K_ON cf= columnFamilyName )
			// Parser.g:912:7: K_DROP K_TRIGGER ( K_IF K_EXISTS )? (name= ident ) K_ON cf= columnFamilyName
			{
			match(input,K_DROP,FOLLOW_K_DROP_in_dropTriggerStatement6168); if (state.failed) return stmt;
			match(input,K_TRIGGER,FOLLOW_K_TRIGGER_in_dropTriggerStatement6170); if (state.failed) return stmt;
			// Parser.g:912:24: ( K_IF K_EXISTS )?
			int alt123=2;
			int LA123_0 = input.LA(1);
			if ( (LA123_0==K_IF) ) {
				alt123=1;
			}
			switch (alt123) {
				case 1 :
					// Parser.g:912:25: K_IF K_EXISTS
					{
					match(input,K_IF,FOLLOW_K_IF_in_dropTriggerStatement6173); if (state.failed) return stmt;
					match(input,K_EXISTS,FOLLOW_K_EXISTS_in_dropTriggerStatement6175); if (state.failed) return stmt;
					if ( state.backtracking==0 ) { ifExists = true; }
					}
					break;

			}

			// Parser.g:912:63: (name= ident )
			// Parser.g:912:64: name= ident
			{
			pushFollow(FOLLOW_ident_in_dropTriggerStatement6185);
			name=ident();
			state._fsp--;
			if (state.failed) return stmt;
			}

			match(input,K_ON,FOLLOW_K_ON_in_dropTriggerStatement6188); if (state.failed) return stmt;
			pushFollow(FOLLOW_columnFamilyName_in_dropTriggerStatement6192);
			cf=columnFamilyName();
			state._fsp--;
			if (state.failed) return stmt;
			if ( state.backtracking==0 ) { stmt = new DropTriggerStatement.Raw(cf, name.toString(), ifExists); }
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return stmt;
	}
	// $ANTLR end "dropTriggerStatement"



	// $ANTLR start "alterKeyspaceStatement"
	// Parser.g:919:1: alterKeyspaceStatement returns [AlterKeyspaceStatement.Raw stmt] : K_ALTER K_KEYSPACE ks= keyspaceName K_WITH properties[attrs] ;
	public final AlterKeyspaceStatement.Raw alterKeyspaceStatement() throws RecognitionException {
		AlterKeyspaceStatement.Raw stmt = null;


		String ks =null;

		 KeyspaceAttributes attrs = new KeyspaceAttributes(); 
		try {
			// Parser.g:921:5: ( K_ALTER K_KEYSPACE ks= keyspaceName K_WITH properties[attrs] )
			// Parser.g:921:7: K_ALTER K_KEYSPACE ks= keyspaceName K_WITH properties[attrs]
			{
			match(input,K_ALTER,FOLLOW_K_ALTER_in_alterKeyspaceStatement6232); if (state.failed) return stmt;
			match(input,K_KEYSPACE,FOLLOW_K_KEYSPACE_in_alterKeyspaceStatement6234); if (state.failed) return stmt;
			pushFollow(FOLLOW_keyspaceName_in_alterKeyspaceStatement6238);
			ks=keyspaceName();
			state._fsp--;
			if (state.failed) return stmt;
			match(input,K_WITH,FOLLOW_K_WITH_in_alterKeyspaceStatement6248); if (state.failed) return stmt;
			pushFollow(FOLLOW_properties_in_alterKeyspaceStatement6250);
			properties(attrs);
			state._fsp--;
			if (state.failed) return stmt;
			if ( state.backtracking==0 ) { stmt = new AlterKeyspaceStatement.Raw(ks, attrs); }
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return stmt;
	}
	// $ANTLR end "alterKeyspaceStatement"



	// $ANTLR start "alterTableStatement"
	// Parser.g:932:1: alterTableStatement returns [AlterTableStatement.Raw stmt] : K_ALTER K_COLUMNFAMILY cf= columnFamilyName ( K_ALTER id= cident K_TYPE v= comparatorType | K_ADD (id= schema_cident v= comparatorType b= isStaticColumn | ( '(' id1= schema_cident v1= comparatorType b1= isStaticColumn ( ',' idn= schema_cident vn= comparatorType bn= isStaticColumn )* ')' ) ) | K_DROP (id= schema_cident | ( '(' id1= schema_cident ( ',' idn= schema_cident )* ')' ) ) ( K_USING K_TIMESTAMP t= INTEGER )? | K_RENAME id1= schema_cident K_TO toId1= schema_cident ( K_AND idn= schema_cident K_TO toIdn= schema_cident )* | K_WITH properties[$stmt.attrs] ) ;
	public final AlterTableStatement.Raw alterTableStatement() throws RecognitionException {
		AlterTableStatement.Raw stmt = null;


		Token t=null;
		QualifiedName cf =null;
		ColumnMetadata.Raw id =null;
		CQL3Type.Raw v =null;
		boolean b =false;
		ColumnMetadata.Raw id1 =null;
		CQL3Type.Raw v1 =null;
		boolean b1 =false;
		ColumnMetadata.Raw idn =null;
		CQL3Type.Raw vn =null;
		boolean bn =false;
		ColumnMetadata.Raw toId1 =null;
		ColumnMetadata.Raw toIdn =null;

		try {
			// Parser.g:933:5: ( K_ALTER K_COLUMNFAMILY cf= columnFamilyName ( K_ALTER id= cident K_TYPE v= comparatorType | K_ADD (id= schema_cident v= comparatorType b= isStaticColumn | ( '(' id1= schema_cident v1= comparatorType b1= isStaticColumn ( ',' idn= schema_cident vn= comparatorType bn= isStaticColumn )* ')' ) ) | K_DROP (id= schema_cident | ( '(' id1= schema_cident ( ',' idn= schema_cident )* ')' ) ) ( K_USING K_TIMESTAMP t= INTEGER )? | K_RENAME id1= schema_cident K_TO toId1= schema_cident ( K_AND idn= schema_cident K_TO toIdn= schema_cident )* | K_WITH properties[$stmt.attrs] ) )
			// Parser.g:933:7: K_ALTER K_COLUMNFAMILY cf= columnFamilyName ( K_ALTER id= cident K_TYPE v= comparatorType | K_ADD (id= schema_cident v= comparatorType b= isStaticColumn | ( '(' id1= schema_cident v1= comparatorType b1= isStaticColumn ( ',' idn= schema_cident vn= comparatorType bn= isStaticColumn )* ')' ) ) | K_DROP (id= schema_cident | ( '(' id1= schema_cident ( ',' idn= schema_cident )* ')' ) ) ( K_USING K_TIMESTAMP t= INTEGER )? | K_RENAME id1= schema_cident K_TO toId1= schema_cident ( K_AND idn= schema_cident K_TO toIdn= schema_cident )* | K_WITH properties[$stmt.attrs] )
			{
			match(input,K_ALTER,FOLLOW_K_ALTER_in_alterTableStatement6276); if (state.failed) return stmt;
			match(input,K_COLUMNFAMILY,FOLLOW_K_COLUMNFAMILY_in_alterTableStatement6278); if (state.failed) return stmt;
			pushFollow(FOLLOW_columnFamilyName_in_alterTableStatement6282);
			cf=columnFamilyName();
			state._fsp--;
			if (state.failed) return stmt;
			if ( state.backtracking==0 ) { stmt = new AlterTableStatement.Raw(cf); }
			// Parser.g:934:7: ( K_ALTER id= cident K_TYPE v= comparatorType | K_ADD (id= schema_cident v= comparatorType b= isStaticColumn | ( '(' id1= schema_cident v1= comparatorType b1= isStaticColumn ( ',' idn= schema_cident vn= comparatorType bn= isStaticColumn )* ')' ) ) | K_DROP (id= schema_cident | ( '(' id1= schema_cident ( ',' idn= schema_cident )* ')' ) ) ( K_USING K_TIMESTAMP t= INTEGER )? | K_RENAME id1= schema_cident K_TO toId1= schema_cident ( K_AND idn= schema_cident K_TO toIdn= schema_cident )* | K_WITH properties[$stmt.attrs] )
			int alt130=5;
			switch ( input.LA(1) ) {
			case K_ALTER:
				{
				alt130=1;
				}
				break;
			case K_ADD:
				{
				alt130=2;
				}
				break;
			case K_DROP:
				{
				alt130=3;
				}
				break;
			case K_RENAME:
				{
				alt130=4;
				}
				break;
			case K_WITH:
				{
				alt130=5;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return stmt;}
				NoViableAltException nvae =
					new NoViableAltException("", 130, 0, input);
				throw nvae;
			}
			switch (alt130) {
				case 1 :
					// Parser.g:935:9: K_ALTER id= cident K_TYPE v= comparatorType
					{
					match(input,K_ALTER,FOLLOW_K_ALTER_in_alterTableStatement6302); if (state.failed) return stmt;
					pushFollow(FOLLOW_cident_in_alterTableStatement6306);
					id=cident();
					state._fsp--;
					if (state.failed) return stmt;
					match(input,K_TYPE,FOLLOW_K_TYPE_in_alterTableStatement6308); if (state.failed) return stmt;
					pushFollow(FOLLOW_comparatorType_in_alterTableStatement6312);
					v=comparatorType();
					state._fsp--;
					if (state.failed) return stmt;
					if ( state.backtracking==0 ) { stmt.alter(id, v); }
					}
					break;
				case 2 :
					// Parser.g:937:9: K_ADD (id= schema_cident v= comparatorType b= isStaticColumn | ( '(' id1= schema_cident v1= comparatorType b1= isStaticColumn ( ',' idn= schema_cident vn= comparatorType bn= isStaticColumn )* ')' ) )
					{
					match(input,K_ADD,FOLLOW_K_ADD_in_alterTableStatement6325); if (state.failed) return stmt;
					// Parser.g:937:16: (id= schema_cident v= comparatorType b= isStaticColumn | ( '(' id1= schema_cident v1= comparatorType b1= isStaticColumn ( ',' idn= schema_cident vn= comparatorType bn= isStaticColumn )* ')' ) )
					int alt125=2;
					int LA125_0 = input.LA(1);
					if ( (LA125_0==IDENT||(LA125_0 >= K_AGGREGATE && LA125_0 <= K_ALL)||LA125_0==K_AS||LA125_0==K_ASCII||(LA125_0 >= K_BIGINT && LA125_0 <= K_BOOLEAN)||(LA125_0 >= K_CALLED && LA125_0 <= K_CLUSTERING)||(LA125_0 >= K_COMPACT && LA125_0 <= K_COUNTER)||LA125_0==K_CUSTOM||(LA125_0 >= K_DATE && LA125_0 <= K_DECIMAL)||(LA125_0 >= K_DISTINCT && LA125_0 <= K_DOUBLE)||LA125_0==K_DURATION||(LA125_0 >= K_EXISTS && LA125_0 <= K_FLOAT)||LA125_0==K_FROZEN||(LA125_0 >= K_FUNCTION && LA125_0 <= K_FUNCTIONS)||LA125_0==K_GROUP||(LA125_0 >= K_INET && LA125_0 <= K_INPUT)||LA125_0==K_INT||(LA125_0 >= K_JSON && LA125_0 <= K_KEYS)||(LA125_0 >= K_KEYSPACES && LA125_0 <= K_LIKE)||(LA125_0 >= K_LIST && LA125_0 <= K_MAP)||LA125_0==K_NOLOGIN||LA125_0==K_NOSUPERUSER||LA125_0==K_OPTIONS||(LA125_0 >= K_PARTITION && LA125_0 <= K_PERMISSIONS)||LA125_0==K_RETURNS||(LA125_0 >= K_ROLE && LA125_0 <= K_ROLES)||(LA125_0 >= K_SFUNC && LA125_0 <= K_TINYINT)||LA125_0==K_TRIGGER||(LA125_0 >= K_TTL && LA125_0 <= K_TYPE)||(LA125_0 >= K_USER && LA125_0 <= K_USERS)||(LA125_0 >= K_UUID && LA125_0 <= K_VARINT)||LA125_0==K_WRITETIME||LA125_0==QUOTED_NAME) ) {
						alt125=1;
					}
					else if ( (LA125_0==190) ) {
						alt125=2;
					}

					else {
						if (state.backtracking>0) {state.failed=true; return stmt;}
						NoViableAltException nvae =
							new NoViableAltException("", 125, 0, input);
						throw nvae;
					}

					switch (alt125) {
						case 1 :
							// Parser.g:937:25: id= schema_cident v= comparatorType b= isStaticColumn
							{
							pushFollow(FOLLOW_schema_cident_in_alterTableStatement6339);
							id=schema_cident();
							state._fsp--;
							if (state.failed) return stmt;
							pushFollow(FOLLOW_comparatorType_in_alterTableStatement6344);
							v=comparatorType();
							state._fsp--;
							if (state.failed) return stmt;
							pushFollow(FOLLOW_isStaticColumn_in_alterTableStatement6349);
							b=isStaticColumn();
							state._fsp--;
							if (state.failed) return stmt;
							if ( state.backtracking==0 ) { stmt.add(id,  v,  b);  }
							}
							break;
						case 2 :
							// Parser.g:938:18: ( '(' id1= schema_cident v1= comparatorType b1= isStaticColumn ( ',' idn= schema_cident vn= comparatorType bn= isStaticColumn )* ')' )
							{
							// Parser.g:938:18: ( '(' id1= schema_cident v1= comparatorType b1= isStaticColumn ( ',' idn= schema_cident vn= comparatorType bn= isStaticColumn )* ')' )
							// Parser.g:938:19: '(' id1= schema_cident v1= comparatorType b1= isStaticColumn ( ',' idn= schema_cident vn= comparatorType bn= isStaticColumn )* ')'
							{
							match(input,190,FOLLOW_190_in_alterTableStatement6371); if (state.failed) return stmt;
							pushFollow(FOLLOW_schema_cident_in_alterTableStatement6376);
							id1=schema_cident();
							state._fsp--;
							if (state.failed) return stmt;
							pushFollow(FOLLOW_comparatorType_in_alterTableStatement6380);
							v1=comparatorType();
							state._fsp--;
							if (state.failed) return stmt;
							pushFollow(FOLLOW_isStaticColumn_in_alterTableStatement6384);
							b1=isStaticColumn();
							state._fsp--;
							if (state.failed) return stmt;
							if ( state.backtracking==0 ) { stmt.add(id1, v1, b1); }
							// Parser.g:939:18: ( ',' idn= schema_cident vn= comparatorType bn= isStaticColumn )*
							loop124:
							while (true) {
								int alt124=2;
								int LA124_0 = input.LA(1);
								if ( (LA124_0==194) ) {
									alt124=1;
								}

								switch (alt124) {
								case 1 :
									// Parser.g:939:20: ',' idn= schema_cident vn= comparatorType bn= isStaticColumn
									{
									match(input,194,FOLLOW_194_in_alterTableStatement6407); if (state.failed) return stmt;
									pushFollow(FOLLOW_schema_cident_in_alterTableStatement6411);
									idn=schema_cident();
									state._fsp--;
									if (state.failed) return stmt;
									pushFollow(FOLLOW_comparatorType_in_alterTableStatement6415);
									vn=comparatorType();
									state._fsp--;
									if (state.failed) return stmt;
									pushFollow(FOLLOW_isStaticColumn_in_alterTableStatement6419);
									bn=isStaticColumn();
									state._fsp--;
									if (state.failed) return stmt;
									if ( state.backtracking==0 ) { stmt.add(idn, vn, bn); }
									}
									break;

								default :
									break loop124;
								}
							}

							match(input,191,FOLLOW_191_in_alterTableStatement6426); if (state.failed) return stmt;
							}

							}
							break;

					}

					}
					break;
				case 3 :
					// Parser.g:941:9: K_DROP (id= schema_cident | ( '(' id1= schema_cident ( ',' idn= schema_cident )* ')' ) ) ( K_USING K_TIMESTAMP t= INTEGER )?
					{
					match(input,K_DROP,FOLLOW_K_DROP_in_alterTableStatement6440); if (state.failed) return stmt;
					// Parser.g:941:16: (id= schema_cident | ( '(' id1= schema_cident ( ',' idn= schema_cident )* ')' ) )
					int alt127=2;
					int LA127_0 = input.LA(1);
					if ( (LA127_0==IDENT||(LA127_0 >= K_AGGREGATE && LA127_0 <= K_ALL)||LA127_0==K_AS||LA127_0==K_ASCII||(LA127_0 >= K_BIGINT && LA127_0 <= K_BOOLEAN)||(LA127_0 >= K_CALLED && LA127_0 <= K_CLUSTERING)||(LA127_0 >= K_COMPACT && LA127_0 <= K_COUNTER)||LA127_0==K_CUSTOM||(LA127_0 >= K_DATE && LA127_0 <= K_DECIMAL)||(LA127_0 >= K_DISTINCT && LA127_0 <= K_DOUBLE)||LA127_0==K_DURATION||(LA127_0 >= K_EXISTS && LA127_0 <= K_FLOAT)||LA127_0==K_FROZEN||(LA127_0 >= K_FUNCTION && LA127_0 <= K_FUNCTIONS)||LA127_0==K_GROUP||(LA127_0 >= K_INET && LA127_0 <= K_INPUT)||LA127_0==K_INT||(LA127_0 >= K_JSON && LA127_0 <= K_KEYS)||(LA127_0 >= K_KEYSPACES && LA127_0 <= K_LIKE)||(LA127_0 >= K_LIST && LA127_0 <= K_MAP)||LA127_0==K_NOLOGIN||LA127_0==K_NOSUPERUSER||LA127_0==K_OPTIONS||(LA127_0 >= K_PARTITION && LA127_0 <= K_PERMISSIONS)||LA127_0==K_RETURNS||(LA127_0 >= K_ROLE && LA127_0 <= K_ROLES)||(LA127_0 >= K_SFUNC && LA127_0 <= K_TINYINT)||LA127_0==K_TRIGGER||(LA127_0 >= K_TTL && LA127_0 <= K_TYPE)||(LA127_0 >= K_USER && LA127_0 <= K_USERS)||(LA127_0 >= K_UUID && LA127_0 <= K_VARINT)||LA127_0==K_WRITETIME||LA127_0==QUOTED_NAME) ) {
						alt127=1;
					}
					else if ( (LA127_0==190) ) {
						alt127=2;
					}

					else {
						if (state.backtracking>0) {state.failed=true; return stmt;}
						NoViableAltException nvae =
							new NoViableAltException("", 127, 0, input);
						throw nvae;
					}

					switch (alt127) {
						case 1 :
							// Parser.g:941:25: id= schema_cident
							{
							pushFollow(FOLLOW_schema_cident_in_alterTableStatement6453);
							id=schema_cident();
							state._fsp--;
							if (state.failed) return stmt;
							if ( state.backtracking==0 ) { stmt.drop(id);  }
							}
							break;
						case 2 :
							// Parser.g:942:18: ( '(' id1= schema_cident ( ',' idn= schema_cident )* ')' )
							{
							// Parser.g:942:18: ( '(' id1= schema_cident ( ',' idn= schema_cident )* ')' )
							// Parser.g:942:19: '(' id1= schema_cident ( ',' idn= schema_cident )* ')'
							{
							match(input,190,FOLLOW_190_in_alterTableStatement6475); if (state.failed) return stmt;
							pushFollow(FOLLOW_schema_cident_in_alterTableStatement6480);
							id1=schema_cident();
							state._fsp--;
							if (state.failed) return stmt;
							if ( state.backtracking==0 ) { stmt.drop(id1); }
							// Parser.g:943:18: ( ',' idn= schema_cident )*
							loop126:
							while (true) {
								int alt126=2;
								int LA126_0 = input.LA(1);
								if ( (LA126_0==194) ) {
									alt126=1;
								}

								switch (alt126) {
								case 1 :
									// Parser.g:943:20: ',' idn= schema_cident
									{
									match(input,194,FOLLOW_194_in_alterTableStatement6503); if (state.failed) return stmt;
									pushFollow(FOLLOW_schema_cident_in_alterTableStatement6507);
									idn=schema_cident();
									state._fsp--;
									if (state.failed) return stmt;
									if ( state.backtracking==0 ) { stmt.drop(idn); }
									}
									break;

								default :
									break loop126;
								}
							}

							match(input,191,FOLLOW_191_in_alterTableStatement6514); if (state.failed) return stmt;
							}

							}
							break;

					}

					// Parser.g:944:16: ( K_USING K_TIMESTAMP t= INTEGER )?
					int alt128=2;
					int LA128_0 = input.LA(1);
					if ( (LA128_0==K_USING) ) {
						alt128=1;
					}
					switch (alt128) {
						case 1 :
							// Parser.g:944:18: K_USING K_TIMESTAMP t= INTEGER
							{
							match(input,K_USING,FOLLOW_K_USING_in_alterTableStatement6536); if (state.failed) return stmt;
							match(input,K_TIMESTAMP,FOLLOW_K_TIMESTAMP_in_alterTableStatement6538); if (state.failed) return stmt;
							t=(Token)match(input,INTEGER,FOLLOW_INTEGER_in_alterTableStatement6542); if (state.failed) return stmt;
							if ( state.backtracking==0 ) { stmt.timestamp(Long.parseLong(Constants.Literal.integer((t!=null?t.getText():null)).getText())); }
							}
							break;

					}

					}
					break;
				case 4 :
					// Parser.g:946:9: K_RENAME id1= schema_cident K_TO toId1= schema_cident ( K_AND idn= schema_cident K_TO toIdn= schema_cident )*
					{
					match(input,K_RENAME,FOLLOW_K_RENAME_in_alterTableStatement6558); if (state.failed) return stmt;
					pushFollow(FOLLOW_schema_cident_in_alterTableStatement6562);
					id1=schema_cident();
					state._fsp--;
					if (state.failed) return stmt;
					match(input,K_TO,FOLLOW_K_TO_in_alterTableStatement6564); if (state.failed) return stmt;
					pushFollow(FOLLOW_schema_cident_in_alterTableStatement6568);
					toId1=schema_cident();
					state._fsp--;
					if (state.failed) return stmt;
					if ( state.backtracking==0 ) { stmt.rename(id1, toId1); }
					// Parser.g:947:10: ( K_AND idn= schema_cident K_TO toIdn= schema_cident )*
					loop129:
					while (true) {
						int alt129=2;
						int LA129_0 = input.LA(1);
						if ( (LA129_0==K_AND) ) {
							alt129=1;
						}

						switch (alt129) {
						case 1 :
							// Parser.g:947:12: K_AND idn= schema_cident K_TO toIdn= schema_cident
							{
							match(input,K_AND,FOLLOW_K_AND_in_alterTableStatement6583); if (state.failed) return stmt;
							pushFollow(FOLLOW_schema_cident_in_alterTableStatement6587);
							idn=schema_cident();
							state._fsp--;
							if (state.failed) return stmt;
							match(input,K_TO,FOLLOW_K_TO_in_alterTableStatement6589); if (state.failed) return stmt;
							pushFollow(FOLLOW_schema_cident_in_alterTableStatement6593);
							toIdn=schema_cident();
							state._fsp--;
							if (state.failed) return stmt;
							if ( state.backtracking==0 ) { stmt.rename(idn, toIdn); }
							}
							break;

						default :
							break loop129;
						}
					}

					}
					break;
				case 5 :
					// Parser.g:949:9: K_WITH properties[$stmt.attrs]
					{
					match(input,K_WITH,FOLLOW_K_WITH_in_alterTableStatement6609); if (state.failed) return stmt;
					pushFollow(FOLLOW_properties_in_alterTableStatement6611);
					properties(stmt.attrs);
					state._fsp--;
					if (state.failed) return stmt;
					if ( state.backtracking==0 ) { stmt.attrs(); }
					}
					break;

			}

			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return stmt;
	}
	// $ANTLR end "alterTableStatement"



	// $ANTLR start "isStaticColumn"
	// Parser.g:953:1: isStaticColumn returns [boolean isStaticColumn] : ( K_STATIC )? ;
	public final boolean isStaticColumn() throws RecognitionException {
		boolean isStaticColumn = false;


		 boolean isStatic = false; 
		try {
			// Parser.g:955:5: ( ( K_STATIC )? )
			// Parser.g:955:7: ( K_STATIC )?
			{
			// Parser.g:955:7: ( K_STATIC )?
			int alt131=2;
			int LA131_0 = input.LA(1);
			if ( (LA131_0==K_STATIC) ) {
				alt131=1;
			}
			switch (alt131) {
				case 1 :
					// Parser.g:955:8: K_STATIC
					{
					match(input,K_STATIC,FOLLOW_K_STATIC_in_isStaticColumn6653); if (state.failed) return isStaticColumn;
					if ( state.backtracking==0 ) { isStatic=true; }
					}
					break;

			}

			if ( state.backtracking==0 ) { isStaticColumn = isStatic; }
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return isStaticColumn;
	}
	// $ANTLR end "isStaticColumn"



	// $ANTLR start "alterMaterializedViewStatement"
	// Parser.g:958:1: alterMaterializedViewStatement returns [AlterViewStatement.Raw stmt] : K_ALTER K_MATERIALIZED K_VIEW name= columnFamilyName K_WITH properties[attrs] ;
	public final AlterViewStatement.Raw alterMaterializedViewStatement() throws RecognitionException {
		AlterViewStatement.Raw stmt = null;


		QualifiedName name =null;


		        TableAttributes attrs = new TableAttributes();
		    
		try {
			// Parser.g:962:5: ( K_ALTER K_MATERIALIZED K_VIEW name= columnFamilyName K_WITH properties[attrs] )
			// Parser.g:962:7: K_ALTER K_MATERIALIZED K_VIEW name= columnFamilyName K_WITH properties[attrs]
			{
			match(input,K_ALTER,FOLLOW_K_ALTER_in_alterMaterializedViewStatement6689); if (state.failed) return stmt;
			match(input,K_MATERIALIZED,FOLLOW_K_MATERIALIZED_in_alterMaterializedViewStatement6691); if (state.failed) return stmt;
			match(input,K_VIEW,FOLLOW_K_VIEW_in_alterMaterializedViewStatement6693); if (state.failed) return stmt;
			pushFollow(FOLLOW_columnFamilyName_in_alterMaterializedViewStatement6697);
			name=columnFamilyName();
			state._fsp--;
			if (state.failed) return stmt;
			match(input,K_WITH,FOLLOW_K_WITH_in_alterMaterializedViewStatement6709); if (state.failed) return stmt;
			pushFollow(FOLLOW_properties_in_alterMaterializedViewStatement6711);
			properties(attrs);
			state._fsp--;
			if (state.failed) return stmt;
			if ( state.backtracking==0 ) {
			        stmt = new AlterViewStatement.Raw(name, attrs);
			    }
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return stmt;
	}
	// $ANTLR end "alterMaterializedViewStatement"



	// $ANTLR start "alterTypeStatement"
	// Parser.g:975:1: alterTypeStatement returns [AlterTypeStatement.Raw stmt] : K_ALTER K_TYPE name= userTypeName ( K_ALTER f= fident K_TYPE v= comparatorType | K_ADD f= fident v= comparatorType | K_RENAME f1= fident K_TO toF1= fident ( K_AND fn= fident K_TO toFn= fident )* ) ;
	public final AlterTypeStatement.Raw alterTypeStatement() throws RecognitionException {
		AlterTypeStatement.Raw stmt = null;


		UTName name =null;
		FieldIdentifier f =null;
		CQL3Type.Raw v =null;
		FieldIdentifier f1 =null;
		FieldIdentifier toF1 =null;
		FieldIdentifier fn =null;
		FieldIdentifier toFn =null;

		try {
			// Parser.g:976:5: ( K_ALTER K_TYPE name= userTypeName ( K_ALTER f= fident K_TYPE v= comparatorType | K_ADD f= fident v= comparatorType | K_RENAME f1= fident K_TO toF1= fident ( K_AND fn= fident K_TO toFn= fident )* ) )
			// Parser.g:976:7: K_ALTER K_TYPE name= userTypeName ( K_ALTER f= fident K_TYPE v= comparatorType | K_ADD f= fident v= comparatorType | K_RENAME f1= fident K_TO toF1= fident ( K_AND fn= fident K_TO toFn= fident )* )
			{
			match(input,K_ALTER,FOLLOW_K_ALTER_in_alterTypeStatement6742); if (state.failed) return stmt;
			match(input,K_TYPE,FOLLOW_K_TYPE_in_alterTypeStatement6744); if (state.failed) return stmt;
			pushFollow(FOLLOW_userTypeName_in_alterTypeStatement6748);
			name=userTypeName();
			state._fsp--;
			if (state.failed) return stmt;
			if ( state.backtracking==0 ) { stmt = new AlterTypeStatement.Raw(name); }
			// Parser.g:977:7: ( K_ALTER f= fident K_TYPE v= comparatorType | K_ADD f= fident v= comparatorType | K_RENAME f1= fident K_TO toF1= fident ( K_AND fn= fident K_TO toFn= fident )* )
			int alt133=3;
			switch ( input.LA(1) ) {
			case K_ALTER:
				{
				alt133=1;
				}
				break;
			case K_ADD:
				{
				alt133=2;
				}
				break;
			case K_RENAME:
				{
				alt133=3;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return stmt;}
				NoViableAltException nvae =
					new NoViableAltException("", 133, 0, input);
				throw nvae;
			}
			switch (alt133) {
				case 1 :
					// Parser.g:978:9: K_ALTER f= fident K_TYPE v= comparatorType
					{
					match(input,K_ALTER,FOLLOW_K_ALTER_in_alterTypeStatement6768); if (state.failed) return stmt;
					pushFollow(FOLLOW_fident_in_alterTypeStatement6774);
					f=fident();
					state._fsp--;
					if (state.failed) return stmt;
					match(input,K_TYPE,FOLLOW_K_TYPE_in_alterTypeStatement6776); if (state.failed) return stmt;
					pushFollow(FOLLOW_comparatorType_in_alterTypeStatement6780);
					v=comparatorType();
					state._fsp--;
					if (state.failed) return stmt;
					if ( state.backtracking==0 ) { stmt.alter(f, v); }
					}
					break;
				case 2 :
					// Parser.g:980:9: K_ADD f= fident v= comparatorType
					{
					match(input,K_ADD,FOLLOW_K_ADD_in_alterTypeStatement6793); if (state.failed) return stmt;
					pushFollow(FOLLOW_fident_in_alterTypeStatement6801);
					f=fident();
					state._fsp--;
					if (state.failed) return stmt;
					pushFollow(FOLLOW_comparatorType_in_alterTypeStatement6805);
					v=comparatorType();
					state._fsp--;
					if (state.failed) return stmt;
					if ( state.backtracking==0 ) { stmt.add(f, v); }
					}
					break;
				case 3 :
					// Parser.g:982:9: K_RENAME f1= fident K_TO toF1= fident ( K_AND fn= fident K_TO toFn= fident )*
					{
					match(input,K_RENAME,FOLLOW_K_RENAME_in_alterTypeStatement6825); if (state.failed) return stmt;
					pushFollow(FOLLOW_fident_in_alterTypeStatement6829);
					f1=fident();
					state._fsp--;
					if (state.failed) return stmt;
					match(input,K_TO,FOLLOW_K_TO_in_alterTypeStatement6831); if (state.failed) return stmt;
					pushFollow(FOLLOW_fident_in_alterTypeStatement6835);
					toF1=fident();
					state._fsp--;
					if (state.failed) return stmt;
					if ( state.backtracking==0 ) { stmt.rename(f1, toF1); }
					// Parser.g:983:10: ( K_AND fn= fident K_TO toFn= fident )*
					loop132:
					while (true) {
						int alt132=2;
						int LA132_0 = input.LA(1);
						if ( (LA132_0==K_AND) ) {
							alt132=1;
						}

						switch (alt132) {
						case 1 :
							// Parser.g:983:12: K_AND fn= fident K_TO toFn= fident
							{
							match(input,K_AND,FOLLOW_K_AND_in_alterTypeStatement6857); if (state.failed) return stmt;
							pushFollow(FOLLOW_fident_in_alterTypeStatement6861);
							fn=fident();
							state._fsp--;
							if (state.failed) return stmt;
							match(input,K_TO,FOLLOW_K_TO_in_alterTypeStatement6863); if (state.failed) return stmt;
							pushFollow(FOLLOW_fident_in_alterTypeStatement6867);
							toFn=fident();
							state._fsp--;
							if (state.failed) return stmt;
							if ( state.backtracking==0 ) { stmt.rename(fn, toFn); }
							}
							break;

						default :
							break loop132;
						}
					}

					}
					break;

			}

			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return stmt;
	}
	// $ANTLR end "alterTypeStatement"



	// $ANTLR start "dropKeyspaceStatement"
	// Parser.g:990:1: dropKeyspaceStatement returns [DropKeyspaceStatement.Raw stmt] : K_DROP K_KEYSPACE ( K_IF K_EXISTS )? ks= keyspaceName ;
	public final DropKeyspaceStatement.Raw dropKeyspaceStatement() throws RecognitionException {
		DropKeyspaceStatement.Raw stmt = null;


		String ks =null;

		 boolean ifExists = false; 
		try {
			// Parser.g:992:5: ( K_DROP K_KEYSPACE ( K_IF K_EXISTS )? ks= keyspaceName )
			// Parser.g:992:7: K_DROP K_KEYSPACE ( K_IF K_EXISTS )? ks= keyspaceName
			{
			match(input,K_DROP,FOLLOW_K_DROP_in_dropKeyspaceStatement6919); if (state.failed) return stmt;
			match(input,K_KEYSPACE,FOLLOW_K_KEYSPACE_in_dropKeyspaceStatement6921); if (state.failed) return stmt;
			// Parser.g:992:25: ( K_IF K_EXISTS )?
			int alt134=2;
			int LA134_0 = input.LA(1);
			if ( (LA134_0==K_IF) ) {
				alt134=1;
			}
			switch (alt134) {
				case 1 :
					// Parser.g:992:26: K_IF K_EXISTS
					{
					match(input,K_IF,FOLLOW_K_IF_in_dropKeyspaceStatement6924); if (state.failed) return stmt;
					match(input,K_EXISTS,FOLLOW_K_EXISTS_in_dropKeyspaceStatement6926); if (state.failed) return stmt;
					if ( state.backtracking==0 ) { ifExists = true; }
					}
					break;

			}

			pushFollow(FOLLOW_keyspaceName_in_dropKeyspaceStatement6935);
			ks=keyspaceName();
			state._fsp--;
			if (state.failed) return stmt;
			if ( state.backtracking==0 ) { stmt = new DropKeyspaceStatement.Raw(ks, ifExists); }
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return stmt;
	}
	// $ANTLR end "dropKeyspaceStatement"



	// $ANTLR start "dropTableStatement"
	// Parser.g:998:1: dropTableStatement returns [DropTableStatement.Raw stmt] : K_DROP K_COLUMNFAMILY ( K_IF K_EXISTS )? name= columnFamilyName ;
	public final DropTableStatement.Raw dropTableStatement() throws RecognitionException {
		DropTableStatement.Raw stmt = null;


		QualifiedName name =null;

		 boolean ifExists = false; 
		try {
			// Parser.g:1000:5: ( K_DROP K_COLUMNFAMILY ( K_IF K_EXISTS )? name= columnFamilyName )
			// Parser.g:1000:7: K_DROP K_COLUMNFAMILY ( K_IF K_EXISTS )? name= columnFamilyName
			{
			match(input,K_DROP,FOLLOW_K_DROP_in_dropTableStatement6969); if (state.failed) return stmt;
			match(input,K_COLUMNFAMILY,FOLLOW_K_COLUMNFAMILY_in_dropTableStatement6971); if (state.failed) return stmt;
			// Parser.g:1000:29: ( K_IF K_EXISTS )?
			int alt135=2;
			int LA135_0 = input.LA(1);
			if ( (LA135_0==K_IF) ) {
				alt135=1;
			}
			switch (alt135) {
				case 1 :
					// Parser.g:1000:30: K_IF K_EXISTS
					{
					match(input,K_IF,FOLLOW_K_IF_in_dropTableStatement6974); if (state.failed) return stmt;
					match(input,K_EXISTS,FOLLOW_K_EXISTS_in_dropTableStatement6976); if (state.failed) return stmt;
					if ( state.backtracking==0 ) { ifExists = true; }
					}
					break;

			}

			pushFollow(FOLLOW_columnFamilyName_in_dropTableStatement6985);
			name=columnFamilyName();
			state._fsp--;
			if (state.failed) return stmt;
			if ( state.backtracking==0 ) { stmt = new DropTableStatement.Raw(name, ifExists); }
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return stmt;
	}
	// $ANTLR end "dropTableStatement"



	// $ANTLR start "dropTypeStatement"
	// Parser.g:1006:1: dropTypeStatement returns [DropTypeStatement.Raw stmt] : K_DROP K_TYPE ( K_IF K_EXISTS )? name= userTypeName ;
	public final DropTypeStatement.Raw dropTypeStatement() throws RecognitionException {
		DropTypeStatement.Raw stmt = null;


		UTName name =null;

		 boolean ifExists = false; 
		try {
			// Parser.g:1008:5: ( K_DROP K_TYPE ( K_IF K_EXISTS )? name= userTypeName )
			// Parser.g:1008:7: K_DROP K_TYPE ( K_IF K_EXISTS )? name= userTypeName
			{
			match(input,K_DROP,FOLLOW_K_DROP_in_dropTypeStatement7019); if (state.failed) return stmt;
			match(input,K_TYPE,FOLLOW_K_TYPE_in_dropTypeStatement7021); if (state.failed) return stmt;
			// Parser.g:1008:21: ( K_IF K_EXISTS )?
			int alt136=2;
			int LA136_0 = input.LA(1);
			if ( (LA136_0==K_IF) ) {
				alt136=1;
			}
			switch (alt136) {
				case 1 :
					// Parser.g:1008:22: K_IF K_EXISTS
					{
					match(input,K_IF,FOLLOW_K_IF_in_dropTypeStatement7024); if (state.failed) return stmt;
					match(input,K_EXISTS,FOLLOW_K_EXISTS_in_dropTypeStatement7026); if (state.failed) return stmt;
					if ( state.backtracking==0 ) { ifExists = true; }
					}
					break;

			}

			pushFollow(FOLLOW_userTypeName_in_dropTypeStatement7035);
			name=userTypeName();
			state._fsp--;
			if (state.failed) return stmt;
			if ( state.backtracking==0 ) { stmt = new DropTypeStatement.Raw(name, ifExists); }
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return stmt;
	}
	// $ANTLR end "dropTypeStatement"



	// $ANTLR start "dropIndexStatement"
	// Parser.g:1014:1: dropIndexStatement returns [DropIndexStatement.Raw stmt] : K_DROP K_INDEX ( K_IF K_EXISTS )? index= indexName ;
	public final DropIndexStatement.Raw dropIndexStatement() throws RecognitionException {
		DropIndexStatement.Raw stmt = null;


		QualifiedName index =null;

		 boolean ifExists = false; 
		try {
			// Parser.g:1016:5: ( K_DROP K_INDEX ( K_IF K_EXISTS )? index= indexName )
			// Parser.g:1016:7: K_DROP K_INDEX ( K_IF K_EXISTS )? index= indexName
			{
			match(input,K_DROP,FOLLOW_K_DROP_in_dropIndexStatement7069); if (state.failed) return stmt;
			match(input,K_INDEX,FOLLOW_K_INDEX_in_dropIndexStatement7071); if (state.failed) return stmt;
			// Parser.g:1016:22: ( K_IF K_EXISTS )?
			int alt137=2;
			int LA137_0 = input.LA(1);
			if ( (LA137_0==K_IF) ) {
				alt137=1;
			}
			switch (alt137) {
				case 1 :
					// Parser.g:1016:23: K_IF K_EXISTS
					{
					match(input,K_IF,FOLLOW_K_IF_in_dropIndexStatement7074); if (state.failed) return stmt;
					match(input,K_EXISTS,FOLLOW_K_EXISTS_in_dropIndexStatement7076); if (state.failed) return stmt;
					if ( state.backtracking==0 ) { ifExists = true; }
					}
					break;

			}

			pushFollow(FOLLOW_indexName_in_dropIndexStatement7085);
			index=indexName();
			state._fsp--;
			if (state.failed) return stmt;
			if ( state.backtracking==0 ) { stmt = new DropIndexStatement.Raw(index, ifExists); }
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return stmt;
	}
	// $ANTLR end "dropIndexStatement"



	// $ANTLR start "dropMaterializedViewStatement"
	// Parser.g:1023:1: dropMaterializedViewStatement returns [DropViewStatement.Raw stmt] : K_DROP K_MATERIALIZED K_VIEW ( K_IF K_EXISTS )? cf= columnFamilyName ;
	public final DropViewStatement.Raw dropMaterializedViewStatement() throws RecognitionException {
		DropViewStatement.Raw stmt = null;


		QualifiedName cf =null;

		 boolean ifExists = false; 
		try {
			// Parser.g:1025:5: ( K_DROP K_MATERIALIZED K_VIEW ( K_IF K_EXISTS )? cf= columnFamilyName )
			// Parser.g:1025:7: K_DROP K_MATERIALIZED K_VIEW ( K_IF K_EXISTS )? cf= columnFamilyName
			{
			match(input,K_DROP,FOLLOW_K_DROP_in_dropMaterializedViewStatement7125); if (state.failed) return stmt;
			match(input,K_MATERIALIZED,FOLLOW_K_MATERIALIZED_in_dropMaterializedViewStatement7127); if (state.failed) return stmt;
			match(input,K_VIEW,FOLLOW_K_VIEW_in_dropMaterializedViewStatement7129); if (state.failed) return stmt;
			// Parser.g:1025:36: ( K_IF K_EXISTS )?
			int alt138=2;
			int LA138_0 = input.LA(1);
			if ( (LA138_0==K_IF) ) {
				alt138=1;
			}
			switch (alt138) {
				case 1 :
					// Parser.g:1025:37: K_IF K_EXISTS
					{
					match(input,K_IF,FOLLOW_K_IF_in_dropMaterializedViewStatement7132); if (state.failed) return stmt;
					match(input,K_EXISTS,FOLLOW_K_EXISTS_in_dropMaterializedViewStatement7134); if (state.failed) return stmt;
					if ( state.backtracking==0 ) { ifExists = true; }
					}
					break;

			}

			pushFollow(FOLLOW_columnFamilyName_in_dropMaterializedViewStatement7143);
			cf=columnFamilyName();
			state._fsp--;
			if (state.failed) return stmt;
			if ( state.backtracking==0 ) { stmt = new DropViewStatement.Raw(cf, ifExists); }
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return stmt;
	}
	// $ANTLR end "dropMaterializedViewStatement"



	// $ANTLR start "truncateStatement"
	// Parser.g:1032:1: truncateStatement returns [TruncateStatement stmt] : K_TRUNCATE ( K_COLUMNFAMILY )? cf= columnFamilyName ;
	public final TruncateStatement truncateStatement() throws RecognitionException {
		TruncateStatement stmt = null;


		QualifiedName cf =null;

		try {
			// Parser.g:1033:5: ( K_TRUNCATE ( K_COLUMNFAMILY )? cf= columnFamilyName )
			// Parser.g:1033:7: K_TRUNCATE ( K_COLUMNFAMILY )? cf= columnFamilyName
			{
			match(input,K_TRUNCATE,FOLLOW_K_TRUNCATE_in_truncateStatement7174); if (state.failed) return stmt;
			// Parser.g:1033:18: ( K_COLUMNFAMILY )?
			int alt139=2;
			int LA139_0 = input.LA(1);
			if ( (LA139_0==K_COLUMNFAMILY) ) {
				alt139=1;
			}
			switch (alt139) {
				case 1 :
					// Parser.g:1033:19: K_COLUMNFAMILY
					{
					match(input,K_COLUMNFAMILY,FOLLOW_K_COLUMNFAMILY_in_truncateStatement7177); if (state.failed) return stmt;
					}
					break;

			}

			pushFollow(FOLLOW_columnFamilyName_in_truncateStatement7183);
			cf=columnFamilyName();
			state._fsp--;
			if (state.failed) return stmt;
			if ( state.backtracking==0 ) { stmt = new TruncateStatement(cf); }
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return stmt;
	}
	// $ANTLR end "truncateStatement"



	// $ANTLR start "grantPermissionsStatement"
	// Parser.g:1039:1: grantPermissionsStatement returns [GrantPermissionsStatement stmt] : K_GRANT permissionOrAll K_ON resource K_TO grantee= userOrRoleName ;
	public final GrantPermissionsStatement grantPermissionsStatement() throws RecognitionException {
		GrantPermissionsStatement stmt = null;


		RoleName grantee =null;
		Set<Permission> permissionOrAll1 =null;
		IResource resource2 =null;

		try {
			// Parser.g:1040:5: ( K_GRANT permissionOrAll K_ON resource K_TO grantee= userOrRoleName )
			// Parser.g:1040:7: K_GRANT permissionOrAll K_ON resource K_TO grantee= userOrRoleName
			{
			match(input,K_GRANT,FOLLOW_K_GRANT_in_grantPermissionsStatement7208); if (state.failed) return stmt;
			pushFollow(FOLLOW_permissionOrAll_in_grantPermissionsStatement7220);
			permissionOrAll1=permissionOrAll();
			state._fsp--;
			if (state.failed) return stmt;
			match(input,K_ON,FOLLOW_K_ON_in_grantPermissionsStatement7228); if (state.failed) return stmt;
			pushFollow(FOLLOW_resource_in_grantPermissionsStatement7240);
			resource2=resource();
			state._fsp--;
			if (state.failed) return stmt;
			match(input,K_TO,FOLLOW_K_TO_in_grantPermissionsStatement7248); if (state.failed) return stmt;
			pushFollow(FOLLOW_userOrRoleName_in_grantPermissionsStatement7262);
			grantee=userOrRoleName();
			state._fsp--;
			if (state.failed) return stmt;
			if ( state.backtracking==0 ) { stmt = new GrantPermissionsStatement(filterPermissions(permissionOrAll1, resource2), resource2, grantee); }
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return stmt;
	}
	// $ANTLR end "grantPermissionsStatement"



	// $ANTLR start "revokePermissionsStatement"
	// Parser.g:1052:1: revokePermissionsStatement returns [RevokePermissionsStatement stmt] : K_REVOKE permissionOrAll K_ON resource K_FROM revokee= userOrRoleName ;
	public final RevokePermissionsStatement revokePermissionsStatement() throws RecognitionException {
		RevokePermissionsStatement stmt = null;


		RoleName revokee =null;
		Set<Permission> permissionOrAll3 =null;
		IResource resource4 =null;

		try {
			// Parser.g:1053:5: ( K_REVOKE permissionOrAll K_ON resource K_FROM revokee= userOrRoleName )
			// Parser.g:1053:7: K_REVOKE permissionOrAll K_ON resource K_FROM revokee= userOrRoleName
			{
			match(input,K_REVOKE,FOLLOW_K_REVOKE_in_revokePermissionsStatement7293); if (state.failed) return stmt;
			pushFollow(FOLLOW_permissionOrAll_in_revokePermissionsStatement7305);
			permissionOrAll3=permissionOrAll();
			state._fsp--;
			if (state.failed) return stmt;
			match(input,K_ON,FOLLOW_K_ON_in_revokePermissionsStatement7313); if (state.failed) return stmt;
			pushFollow(FOLLOW_resource_in_revokePermissionsStatement7325);
			resource4=resource();
			state._fsp--;
			if (state.failed) return stmt;
			match(input,K_FROM,FOLLOW_K_FROM_in_revokePermissionsStatement7333); if (state.failed) return stmt;
			pushFollow(FOLLOW_userOrRoleName_in_revokePermissionsStatement7347);
			revokee=userOrRoleName();
			state._fsp--;
			if (state.failed) return stmt;
			if ( state.backtracking==0 ) { stmt = new RevokePermissionsStatement(filterPermissions(permissionOrAll3, resource4), resource4, revokee); }
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return stmt;
	}
	// $ANTLR end "revokePermissionsStatement"



	// $ANTLR start "grantRoleStatement"
	// Parser.g:1065:1: grantRoleStatement returns [GrantRoleStatement stmt] : K_GRANT role= userOrRoleName K_TO grantee= userOrRoleName ;
	public final GrantRoleStatement grantRoleStatement() throws RecognitionException {
		GrantRoleStatement stmt = null;


		RoleName role =null;
		RoleName grantee =null;

		try {
			// Parser.g:1066:5: ( K_GRANT role= userOrRoleName K_TO grantee= userOrRoleName )
			// Parser.g:1066:7: K_GRANT role= userOrRoleName K_TO grantee= userOrRoleName
			{
			match(input,K_GRANT,FOLLOW_K_GRANT_in_grantRoleStatement7378); if (state.failed) return stmt;
			pushFollow(FOLLOW_userOrRoleName_in_grantRoleStatement7392);
			role=userOrRoleName();
			state._fsp--;
			if (state.failed) return stmt;
			match(input,K_TO,FOLLOW_K_TO_in_grantRoleStatement7400); if (state.failed) return stmt;
			pushFollow(FOLLOW_userOrRoleName_in_grantRoleStatement7414);
			grantee=userOrRoleName();
			state._fsp--;
			if (state.failed) return stmt;
			if ( state.backtracking==0 ) { stmt = new GrantRoleStatement(role, grantee); }
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return stmt;
	}
	// $ANTLR end "grantRoleStatement"



	// $ANTLR start "revokeRoleStatement"
	// Parser.g:1076:1: revokeRoleStatement returns [RevokeRoleStatement stmt] : K_REVOKE role= userOrRoleName K_FROM revokee= userOrRoleName ;
	public final RevokeRoleStatement revokeRoleStatement() throws RecognitionException {
		RevokeRoleStatement stmt = null;


		RoleName role =null;
		RoleName revokee =null;

		try {
			// Parser.g:1077:5: ( K_REVOKE role= userOrRoleName K_FROM revokee= userOrRoleName )
			// Parser.g:1077:7: K_REVOKE role= userOrRoleName K_FROM revokee= userOrRoleName
			{
			match(input,K_REVOKE,FOLLOW_K_REVOKE_in_revokeRoleStatement7445); if (state.failed) return stmt;
			pushFollow(FOLLOW_userOrRoleName_in_revokeRoleStatement7459);
			role=userOrRoleName();
			state._fsp--;
			if (state.failed) return stmt;
			match(input,K_FROM,FOLLOW_K_FROM_in_revokeRoleStatement7467); if (state.failed) return stmt;
			pushFollow(FOLLOW_userOrRoleName_in_revokeRoleStatement7481);
			revokee=userOrRoleName();
			state._fsp--;
			if (state.failed) return stmt;
			if ( state.backtracking==0 ) { stmt = new RevokeRoleStatement(role, revokee); }
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return stmt;
	}
	// $ANTLR end "revokeRoleStatement"



	// $ANTLR start "listPermissionsStatement"
	// Parser.g:1084:1: listPermissionsStatement returns [ListPermissionsStatement stmt] : K_LIST permissionOrAll ( K_ON resource )? ( K_OF roleName[grantee] )? ( K_NORECURSIVE )? ;
	public final ListPermissionsStatement listPermissionsStatement() throws RecognitionException {
		ListPermissionsStatement stmt = null;


		IResource resource5 =null;
		Set<Permission> permissionOrAll6 =null;


		        IResource resource = null;
		        boolean recursive = true;
		        RoleName grantee = new RoleName();
		    
		try {
			// Parser.g:1090:5: ( K_LIST permissionOrAll ( K_ON resource )? ( K_OF roleName[grantee] )? ( K_NORECURSIVE )? )
			// Parser.g:1090:7: K_LIST permissionOrAll ( K_ON resource )? ( K_OF roleName[grantee] )? ( K_NORECURSIVE )?
			{
			match(input,K_LIST,FOLLOW_K_LIST_in_listPermissionsStatement7519); if (state.failed) return stmt;
			pushFollow(FOLLOW_permissionOrAll_in_listPermissionsStatement7531);
			permissionOrAll6=permissionOrAll();
			state._fsp--;
			if (state.failed) return stmt;
			// Parser.g:1092:7: ( K_ON resource )?
			int alt140=2;
			int LA140_0 = input.LA(1);
			if ( (LA140_0==K_ON) ) {
				alt140=1;
			}
			switch (alt140) {
				case 1 :
					// Parser.g:1092:9: K_ON resource
					{
					match(input,K_ON,FOLLOW_K_ON_in_listPermissionsStatement7541); if (state.failed) return stmt;
					pushFollow(FOLLOW_resource_in_listPermissionsStatement7543);
					resource5=resource();
					state._fsp--;
					if (state.failed) return stmt;
					if ( state.backtracking==0 ) { resource = resource5; }
					}
					break;

			}

			// Parser.g:1093:7: ( K_OF roleName[grantee] )?
			int alt141=2;
			int LA141_0 = input.LA(1);
			if ( (LA141_0==K_OF) ) {
				alt141=1;
			}
			switch (alt141) {
				case 1 :
					// Parser.g:1093:9: K_OF roleName[grantee]
					{
					match(input,K_OF,FOLLOW_K_OF_in_listPermissionsStatement7558); if (state.failed) return stmt;
					pushFollow(FOLLOW_roleName_in_listPermissionsStatement7560);
					roleName(grantee);
					state._fsp--;
					if (state.failed) return stmt;
					}
					break;

			}

			// Parser.g:1094:7: ( K_NORECURSIVE )?
			int alt142=2;
			int LA142_0 = input.LA(1);
			if ( (LA142_0==K_NORECURSIVE) ) {
				alt142=1;
			}
			switch (alt142) {
				case 1 :
					// Parser.g:1094:9: K_NORECURSIVE
					{
					match(input,K_NORECURSIVE,FOLLOW_K_NORECURSIVE_in_listPermissionsStatement7574); if (state.failed) return stmt;
					if ( state.backtracking==0 ) { recursive = false; }
					}
					break;

			}

			if ( state.backtracking==0 ) { stmt = new ListPermissionsStatement(permissionOrAll6, resource, grantee, recursive); }
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return stmt;
	}
	// $ANTLR end "listPermissionsStatement"



	// $ANTLR start "permission"
	// Parser.g:1098:1: permission returns [Permission perm] : p= ( K_CREATE | K_ALTER | K_DROP | K_SELECT | K_MODIFY | K_AUTHORIZE | K_DESCRIBE | K_EXECUTE ) ;
	public final Permission permission() throws RecognitionException {
		Permission perm = null;


		Token p=null;

		try {
			// Parser.g:1099:5: (p= ( K_CREATE | K_ALTER | K_DROP | K_SELECT | K_MODIFY | K_AUTHORIZE | K_DESCRIBE | K_EXECUTE ) )
			// Parser.g:1099:7: p= ( K_CREATE | K_ALTER | K_DROP | K_SELECT | K_MODIFY | K_AUTHORIZE | K_DESCRIBE | K_EXECUTE )
			{
			p=input.LT(1);
			if ( input.LA(1)==K_ALTER||input.LA(1)==K_AUTHORIZE||input.LA(1)==K_CREATE||input.LA(1)==K_DESCRIBE||input.LA(1)==K_DROP||input.LA(1)==K_EXECUTE||input.LA(1)==K_MODIFY||input.LA(1)==K_SELECT ) {
				input.consume();
				state.errorRecovery=false;
				state.failed=false;
			}
			else {
				if (state.backtracking>0) {state.failed=true; return perm;}
				MismatchedSetException mse = new MismatchedSetException(null,input);
				throw mse;
			}
			if ( state.backtracking==0 ) { perm = Permission.valueOf((p!=null?p.getText():null).toUpperCase()); }
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return perm;
	}
	// $ANTLR end "permission"



	// $ANTLR start "permissionOrAll"
	// Parser.g:1103:1: permissionOrAll returns [Set<Permission> perms] : ( K_ALL ( K_PERMISSIONS )? |p= permission ( K_PERMISSION )? );
	public final Set<Permission> permissionOrAll() throws RecognitionException {
		Set<Permission> perms = null;


		Permission p =null;

		try {
			// Parser.g:1104:5: ( K_ALL ( K_PERMISSIONS )? |p= permission ( K_PERMISSION )? )
			int alt145=2;
			int LA145_0 = input.LA(1);
			if ( (LA145_0==K_ALL) ) {
				alt145=1;
			}
			else if ( (LA145_0==K_ALTER||LA145_0==K_AUTHORIZE||LA145_0==K_CREATE||LA145_0==K_DESCRIBE||LA145_0==K_DROP||LA145_0==K_EXECUTE||LA145_0==K_MODIFY||LA145_0==K_SELECT) ) {
				alt145=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return perms;}
				NoViableAltException nvae =
					new NoViableAltException("", 145, 0, input);
				throw nvae;
			}

			switch (alt145) {
				case 1 :
					// Parser.g:1104:7: K_ALL ( K_PERMISSIONS )?
					{
					match(input,K_ALL,FOLLOW_K_ALL_in_permissionOrAll7667); if (state.failed) return perms;
					// Parser.g:1104:13: ( K_PERMISSIONS )?
					int alt143=2;
					int LA143_0 = input.LA(1);
					if ( (LA143_0==K_PERMISSIONS) ) {
						alt143=1;
					}
					switch (alt143) {
						case 1 :
							// Parser.g:1104:15: K_PERMISSIONS
							{
							match(input,K_PERMISSIONS,FOLLOW_K_PERMISSIONS_in_permissionOrAll7671); if (state.failed) return perms;
							}
							break;

					}

					if ( state.backtracking==0 ) { perms = Permission.ALL; }
					}
					break;
				case 2 :
					// Parser.g:1105:7: p= permission ( K_PERMISSION )?
					{
					pushFollow(FOLLOW_permission_in_permissionOrAll7692);
					p=permission();
					state._fsp--;
					if (state.failed) return perms;
					// Parser.g:1105:20: ( K_PERMISSION )?
					int alt144=2;
					int LA144_0 = input.LA(1);
					if ( (LA144_0==K_PERMISSION) ) {
						alt144=1;
					}
					switch (alt144) {
						case 1 :
							// Parser.g:1105:22: K_PERMISSION
							{
							match(input,K_PERMISSION,FOLLOW_K_PERMISSION_in_permissionOrAll7696); if (state.failed) return perms;
							}
							break;

					}

					if ( state.backtracking==0 ) { perms = EnumSet.of(p); }
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return perms;
	}
	// $ANTLR end "permissionOrAll"



	// $ANTLR start "resource"
	// Parser.g:1108:1: resource returns [IResource res] : (d= dataResource |r= roleResource |f= functionResource |j= jmxResource );
	public final IResource resource() throws RecognitionException {
		IResource res = null;


		DataResource d =null;
		RoleResource r =null;
		FunctionResource f =null;
		JMXResource j =null;

		try {
			// Parser.g:1109:5: (d= dataResource |r= roleResource |f= functionResource |j= jmxResource )
			int alt146=4;
			switch ( input.LA(1) ) {
			case K_ALL:
				{
				switch ( input.LA(2) ) {
				case EOF:
				case K_FROM:
				case K_KEYSPACES:
				case K_NORECURSIVE:
				case K_OF:
				case K_TO:
				case 197:
				case 200:
					{
					alt146=1;
					}
					break;
				case K_ROLES:
					{
					alt146=2;
					}
					break;
				case K_FUNCTIONS:
					{
					alt146=3;
					}
					break;
				case K_MBEANS:
					{
					alt146=4;
					}
					break;
				default:
					if (state.backtracking>0) {state.failed=true; return res;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 146, 1, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}
				}
				break;
			case IDENT:
			case K_AGGREGATE:
			case K_AS:
			case K_ASCII:
			case K_BIGINT:
			case K_BLOB:
			case K_BOOLEAN:
			case K_CALLED:
			case K_CAST:
			case K_CLUSTERING:
			case K_COLUMNFAMILY:
			case K_COMPACT:
			case K_CONTAINS:
			case K_COUNT:
			case K_COUNTER:
			case K_CUSTOM:
			case K_DATE:
			case K_DECIMAL:
			case K_DISTINCT:
			case K_DOUBLE:
			case K_DURATION:
			case K_EXISTS:
			case K_FILTERING:
			case K_FINALFUNC:
			case K_FLOAT:
			case K_FROZEN:
			case K_FUNCTIONS:
			case K_GROUP:
			case K_INET:
			case K_INITCOND:
			case K_INPUT:
			case K_INT:
			case K_JSON:
			case K_KEY:
			case K_KEYS:
			case K_KEYSPACE:
			case K_KEYSPACES:
			case K_LANGUAGE:
			case K_LIKE:
			case K_LIST:
			case K_LOGIN:
			case K_MAP:
			case K_NOLOGIN:
			case K_NOSUPERUSER:
			case K_OPTIONS:
			case K_PARTITION:
			case K_PASSWORD:
			case K_PER:
			case K_PERMISSION:
			case K_PERMISSIONS:
			case K_RETURNS:
			case K_ROLES:
			case K_SFUNC:
			case K_SMALLINT:
			case K_STATIC:
			case K_STORAGE:
			case K_STYPE:
			case K_SUPERUSER:
			case K_TEXT:
			case K_TIME:
			case K_TIMESTAMP:
			case K_TIMEUUID:
			case K_TINYINT:
			case K_TRIGGER:
			case K_TTL:
			case K_TUPLE:
			case K_TYPE:
			case K_USER:
			case K_USERS:
			case K_UUID:
			case K_VALUES:
			case K_VARCHAR:
			case K_VARINT:
			case K_WRITETIME:
			case QMARK:
			case QUOTED_NAME:
				{
				alt146=1;
				}
				break;
			case K_ROLE:
				{
				int LA146_3 = input.LA(2);
				if ( (LA146_3==EOF||LA146_3==K_FROM||LA146_3==K_NORECURSIVE||LA146_3==K_OF||LA146_3==K_TO||LA146_3==197||LA146_3==200) ) {
					alt146=1;
				}
				else if ( (LA146_3==IDENT||(LA146_3 >= K_AGGREGATE && LA146_3 <= K_ALL)||LA146_3==K_AS||LA146_3==K_ASCII||(LA146_3 >= K_BIGINT && LA146_3 <= K_BOOLEAN)||(LA146_3 >= K_CALLED && LA146_3 <= K_CLUSTERING)||(LA146_3 >= K_COMPACT && LA146_3 <= K_COUNTER)||LA146_3==K_CUSTOM||(LA146_3 >= K_DATE && LA146_3 <= K_DECIMAL)||(LA146_3 >= K_DISTINCT && LA146_3 <= K_DOUBLE)||LA146_3==K_DURATION||(LA146_3 >= K_EXISTS && LA146_3 <= K_FLOAT)||LA146_3==K_FROZEN||(LA146_3 >= K_FUNCTION && LA146_3 <= K_FUNCTIONS)||LA146_3==K_GROUP||(LA146_3 >= K_INET && LA146_3 <= K_INPUT)||LA146_3==K_INT||(LA146_3 >= K_JSON && LA146_3 <= K_KEYS)||(LA146_3 >= K_KEYSPACES && LA146_3 <= K_LIKE)||(LA146_3 >= K_LIST && LA146_3 <= K_MAP)||LA146_3==K_NOLOGIN||LA146_3==K_NOSUPERUSER||LA146_3==K_OPTIONS||(LA146_3 >= K_PARTITION && LA146_3 <= K_PERMISSIONS)||LA146_3==K_RETURNS||(LA146_3 >= K_ROLE && LA146_3 <= K_ROLES)||(LA146_3 >= K_SFUNC && LA146_3 <= K_TINYINT)||LA146_3==K_TRIGGER||(LA146_3 >= K_TTL && LA146_3 <= K_TYPE)||(LA146_3 >= K_USER && LA146_3 <= K_USERS)||(LA146_3 >= K_UUID && LA146_3 <= K_VARINT)||LA146_3==K_WRITETIME||(LA146_3 >= QMARK && LA146_3 <= QUOTED_NAME)||LA146_3==STRING_LITERAL) ) {
					alt146=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return res;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 146, 3, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case K_FUNCTION:
				{
				int LA146_4 = input.LA(2);
				if ( (LA146_4==EOF||LA146_4==K_FROM||LA146_4==K_NORECURSIVE||LA146_4==K_OF||LA146_4==K_TO||LA146_4==197||LA146_4==200) ) {
					alt146=1;
				}
				else if ( (LA146_4==IDENT||(LA146_4 >= K_AGGREGATE && LA146_4 <= K_ALL)||LA146_4==K_AS||LA146_4==K_ASCII||(LA146_4 >= K_BIGINT && LA146_4 <= K_BOOLEAN)||(LA146_4 >= K_CALLED && LA146_4 <= K_CLUSTERING)||(LA146_4 >= K_COMPACT && LA146_4 <= K_COUNTER)||LA146_4==K_CUSTOM||(LA146_4 >= K_DATE && LA146_4 <= K_DECIMAL)||(LA146_4 >= K_DISTINCT && LA146_4 <= K_DOUBLE)||LA146_4==K_DURATION||(LA146_4 >= K_EXISTS && LA146_4 <= K_FLOAT)||LA146_4==K_FROZEN||(LA146_4 >= K_FUNCTION && LA146_4 <= K_FUNCTIONS)||LA146_4==K_GROUP||(LA146_4 >= K_INET && LA146_4 <= K_INPUT)||LA146_4==K_INT||(LA146_4 >= K_JSON && LA146_4 <= K_KEYS)||(LA146_4 >= K_KEYSPACES && LA146_4 <= K_LIKE)||(LA146_4 >= K_LIST && LA146_4 <= K_MAP)||LA146_4==K_NOLOGIN||LA146_4==K_NOSUPERUSER||LA146_4==K_OPTIONS||(LA146_4 >= K_PARTITION && LA146_4 <= K_PERMISSIONS)||LA146_4==K_RETURNS||(LA146_4 >= K_ROLE && LA146_4 <= K_ROLES)||(LA146_4 >= K_SFUNC && LA146_4 <= K_TINYINT)||(LA146_4 >= K_TOKEN && LA146_4 <= K_TRIGGER)||(LA146_4 >= K_TTL && LA146_4 <= K_TYPE)||(LA146_4 >= K_USER && LA146_4 <= K_USERS)||(LA146_4 >= K_UUID && LA146_4 <= K_VARINT)||LA146_4==K_WRITETIME||(LA146_4 >= QMARK && LA146_4 <= QUOTED_NAME)) ) {
					alt146=3;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return res;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 146, 4, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case K_MBEAN:
			case K_MBEANS:
				{
				alt146=4;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return res;}
				NoViableAltException nvae =
					new NoViableAltException("", 146, 0, input);
				throw nvae;
			}
			switch (alt146) {
				case 1 :
					// Parser.g:1109:7: d= dataResource
					{
					pushFollow(FOLLOW_dataResource_in_resource7724);
					d=dataResource();
					state._fsp--;
					if (state.failed) return res;
					if ( state.backtracking==0 ) { res = d; }
					}
					break;
				case 2 :
					// Parser.g:1110:7: r= roleResource
					{
					pushFollow(FOLLOW_roleResource_in_resource7736);
					r=roleResource();
					state._fsp--;
					if (state.failed) return res;
					if ( state.backtracking==0 ) { res = r; }
					}
					break;
				case 3 :
					// Parser.g:1111:7: f= functionResource
					{
					pushFollow(FOLLOW_functionResource_in_resource7748);
					f=functionResource();
					state._fsp--;
					if (state.failed) return res;
					if ( state.backtracking==0 ) { res = f; }
					}
					break;
				case 4 :
					// Parser.g:1112:7: j= jmxResource
					{
					pushFollow(FOLLOW_jmxResource_in_resource7760);
					j=jmxResource();
					state._fsp--;
					if (state.failed) return res;
					if ( state.backtracking==0 ) { res = j; }
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return res;
	}
	// $ANTLR end "resource"



	// $ANTLR start "dataResource"
	// Parser.g:1115:1: dataResource returns [DataResource res] : ( K_ALL K_KEYSPACES | K_KEYSPACE ks= keyspaceName | ( K_COLUMNFAMILY )? cf= columnFamilyName );
	public final DataResource dataResource() throws RecognitionException {
		DataResource res = null;


		String ks =null;
		QualifiedName cf =null;

		try {
			// Parser.g:1116:5: ( K_ALL K_KEYSPACES | K_KEYSPACE ks= keyspaceName | ( K_COLUMNFAMILY )? cf= columnFamilyName )
			int alt148=3;
			switch ( input.LA(1) ) {
			case K_ALL:
				{
				int LA148_1 = input.LA(2);
				if ( (LA148_1==K_KEYSPACES) ) {
					alt148=1;
				}
				else if ( (LA148_1==EOF||LA148_1==K_FROM||LA148_1==K_NORECURSIVE||LA148_1==K_OF||LA148_1==K_TO||LA148_1==197||LA148_1==200) ) {
					alt148=3;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return res;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 148, 1, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case K_KEYSPACE:
				{
				alt148=2;
				}
				break;
			case IDENT:
			case K_AGGREGATE:
			case K_AS:
			case K_ASCII:
			case K_BIGINT:
			case K_BLOB:
			case K_BOOLEAN:
			case K_CALLED:
			case K_CAST:
			case K_CLUSTERING:
			case K_COLUMNFAMILY:
			case K_COMPACT:
			case K_CONTAINS:
			case K_COUNT:
			case K_COUNTER:
			case K_CUSTOM:
			case K_DATE:
			case K_DECIMAL:
			case K_DISTINCT:
			case K_DOUBLE:
			case K_DURATION:
			case K_EXISTS:
			case K_FILTERING:
			case K_FINALFUNC:
			case K_FLOAT:
			case K_FROZEN:
			case K_FUNCTION:
			case K_FUNCTIONS:
			case K_GROUP:
			case K_INET:
			case K_INITCOND:
			case K_INPUT:
			case K_INT:
			case K_JSON:
			case K_KEY:
			case K_KEYS:
			case K_KEYSPACES:
			case K_LANGUAGE:
			case K_LIKE:
			case K_LIST:
			case K_LOGIN:
			case K_MAP:
			case K_NOLOGIN:
			case K_NOSUPERUSER:
			case K_OPTIONS:
			case K_PARTITION:
			case K_PASSWORD:
			case K_PER:
			case K_PERMISSION:
			case K_PERMISSIONS:
			case K_RETURNS:
			case K_ROLE:
			case K_ROLES:
			case K_SFUNC:
			case K_SMALLINT:
			case K_STATIC:
			case K_STORAGE:
			case K_STYPE:
			case K_SUPERUSER:
			case K_TEXT:
			case K_TIME:
			case K_TIMESTAMP:
			case K_TIMEUUID:
			case K_TINYINT:
			case K_TRIGGER:
			case K_TTL:
			case K_TUPLE:
			case K_TYPE:
			case K_USER:
			case K_USERS:
			case K_UUID:
			case K_VALUES:
			case K_VARCHAR:
			case K_VARINT:
			case K_WRITETIME:
			case QMARK:
			case QUOTED_NAME:
				{
				alt148=3;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return res;}
				NoViableAltException nvae =
					new NoViableAltException("", 148, 0, input);
				throw nvae;
			}
			switch (alt148) {
				case 1 :
					// Parser.g:1116:7: K_ALL K_KEYSPACES
					{
					match(input,K_ALL,FOLLOW_K_ALL_in_dataResource7783); if (state.failed) return res;
					match(input,K_KEYSPACES,FOLLOW_K_KEYSPACES_in_dataResource7785); if (state.failed) return res;
					if ( state.backtracking==0 ) { res = DataResource.root(); }
					}
					break;
				case 2 :
					// Parser.g:1117:7: K_KEYSPACE ks= keyspaceName
					{
					match(input,K_KEYSPACE,FOLLOW_K_KEYSPACE_in_dataResource7795); if (state.failed) return res;
					pushFollow(FOLLOW_keyspaceName_in_dataResource7801);
					ks=keyspaceName();
					state._fsp--;
					if (state.failed) return res;
					if ( state.backtracking==0 ) { res = DataResource.keyspace(ks); }
					}
					break;
				case 3 :
					// Parser.g:1118:7: ( K_COLUMNFAMILY )? cf= columnFamilyName
					{
					// Parser.g:1118:7: ( K_COLUMNFAMILY )?
					int alt147=2;
					int LA147_0 = input.LA(1);
					if ( (LA147_0==K_COLUMNFAMILY) ) {
						alt147=1;
					}
					switch (alt147) {
						case 1 :
							// Parser.g:1118:9: K_COLUMNFAMILY
							{
							match(input,K_COLUMNFAMILY,FOLLOW_K_COLUMNFAMILY_in_dataResource7813); if (state.failed) return res;
							}
							break;

					}

					pushFollow(FOLLOW_columnFamilyName_in_dataResource7822);
					cf=columnFamilyName();
					state._fsp--;
					if (state.failed) return res;
					if ( state.backtracking==0 ) { res = DataResource.table(cf.getKeyspace(), cf.getName()); }
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return res;
	}
	// $ANTLR end "dataResource"



	// $ANTLR start "jmxResource"
	// Parser.g:1122:1: jmxResource returns [JMXResource res] : ( K_ALL K_MBEANS | K_MBEAN mbean | K_MBEANS mbean );
	public final JMXResource jmxResource() throws RecognitionException {
		JMXResource res = null;


		ParserRuleReturnScope mbean7 =null;
		ParserRuleReturnScope mbean8 =null;

		try {
			// Parser.g:1123:5: ( K_ALL K_MBEANS | K_MBEAN mbean | K_MBEANS mbean )
			int alt149=3;
			switch ( input.LA(1) ) {
			case K_ALL:
				{
				alt149=1;
				}
				break;
			case K_MBEAN:
				{
				alt149=2;
				}
				break;
			case K_MBEANS:
				{
				alt149=3;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return res;}
				NoViableAltException nvae =
					new NoViableAltException("", 149, 0, input);
				throw nvae;
			}
			switch (alt149) {
				case 1 :
					// Parser.g:1123:7: K_ALL K_MBEANS
					{
					match(input,K_ALL,FOLLOW_K_ALL_in_jmxResource7851); if (state.failed) return res;
					match(input,K_MBEANS,FOLLOW_K_MBEANS_in_jmxResource7853); if (state.failed) return res;
					if ( state.backtracking==0 ) { res = JMXResource.root(); }
					}
					break;
				case 2 :
					// Parser.g:1126:7: K_MBEAN mbean
					{
					match(input,K_MBEAN,FOLLOW_K_MBEAN_in_jmxResource7873); if (state.failed) return res;
					pushFollow(FOLLOW_mbean_in_jmxResource7875);
					mbean7=mbean();
					state._fsp--;
					if (state.failed) return res;
					if ( state.backtracking==0 ) { res = JMXResource.mbean(canonicalizeObjectName((mbean7!=null?input.toString(mbean7.start,mbean7.stop):null), false)); }
					}
					break;
				case 3 :
					// Parser.g:1127:7: K_MBEANS mbean
					{
					match(input,K_MBEANS,FOLLOW_K_MBEANS_in_jmxResource7885); if (state.failed) return res;
					pushFollow(FOLLOW_mbean_in_jmxResource7887);
					mbean8=mbean();
					state._fsp--;
					if (state.failed) return res;
					if ( state.backtracking==0 ) { res = JMXResource.mbean(canonicalizeObjectName((mbean8!=null?input.toString(mbean8.start,mbean8.stop):null), true)); }
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return res;
	}
	// $ANTLR end "jmxResource"



	// $ANTLR start "roleResource"
	// Parser.g:1130:1: roleResource returns [RoleResource res] : ( K_ALL K_ROLES | K_ROLE role= userOrRoleName );
	public final RoleResource roleResource() throws RecognitionException {
		RoleResource res = null;


		RoleName role =null;

		try {
			// Parser.g:1131:5: ( K_ALL K_ROLES | K_ROLE role= userOrRoleName )
			int alt150=2;
			int LA150_0 = input.LA(1);
			if ( (LA150_0==K_ALL) ) {
				alt150=1;
			}
			else if ( (LA150_0==K_ROLE) ) {
				alt150=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return res;}
				NoViableAltException nvae =
					new NoViableAltException("", 150, 0, input);
				throw nvae;
			}

			switch (alt150) {
				case 1 :
					// Parser.g:1131:7: K_ALL K_ROLES
					{
					match(input,K_ALL,FOLLOW_K_ALL_in_roleResource7910); if (state.failed) return res;
					match(input,K_ROLES,FOLLOW_K_ROLES_in_roleResource7912); if (state.failed) return res;
					if ( state.backtracking==0 ) { res = RoleResource.root(); }
					}
					break;
				case 2 :
					// Parser.g:1132:7: K_ROLE role= userOrRoleName
					{
					match(input,K_ROLE,FOLLOW_K_ROLE_in_roleResource7922); if (state.failed) return res;
					pushFollow(FOLLOW_userOrRoleName_in_roleResource7928);
					role=userOrRoleName();
					state._fsp--;
					if (state.failed) return res;
					if ( state.backtracking==0 ) { res = RoleResource.role(role.getName()); }
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return res;
	}
	// $ANTLR end "roleResource"



	// $ANTLR start "functionResource"
	// Parser.g:1135:1: functionResource returns [FunctionResource res] : ( K_ALL K_FUNCTIONS | K_ALL K_FUNCTIONS K_IN K_KEYSPACE ks= keyspaceName | K_FUNCTION fn= functionName ( '(' (v= comparatorType ( ',' v= comparatorType )* )? ')' ) );
	public final FunctionResource functionResource() throws RecognitionException {
		FunctionResource res = null;


		String ks =null;
		FunctionName fn =null;
		CQL3Type.Raw v =null;


		        List<CQL3Type.Raw> argsTypes = new ArrayList<>();
		    
		try {
			// Parser.g:1139:5: ( K_ALL K_FUNCTIONS | K_ALL K_FUNCTIONS K_IN K_KEYSPACE ks= keyspaceName | K_FUNCTION fn= functionName ( '(' (v= comparatorType ( ',' v= comparatorType )* )? ')' ) )
			int alt153=3;
			int LA153_0 = input.LA(1);
			if ( (LA153_0==K_ALL) ) {
				int LA153_1 = input.LA(2);
				if ( (LA153_1==K_FUNCTIONS) ) {
					int LA153_3 = input.LA(3);
					if ( (LA153_3==K_IN) ) {
						alt153=2;
					}
					else if ( (LA153_3==EOF||LA153_3==K_FROM||LA153_3==K_NORECURSIVE||LA153_3==K_OF||LA153_3==K_TO||LA153_3==200) ) {
						alt153=1;
					}

					else {
						if (state.backtracking>0) {state.failed=true; return res;}
						int nvaeMark = input.mark();
						try {
							for (int nvaeConsume = 0; nvaeConsume < 3 - 1; nvaeConsume++) {
								input.consume();
							}
							NoViableAltException nvae =
								new NoViableAltException("", 153, 3, input);
							throw nvae;
						} finally {
							input.rewind(nvaeMark);
						}
					}

				}

				else {
					if (state.backtracking>0) {state.failed=true; return res;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 153, 1, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

			}
			else if ( (LA153_0==K_FUNCTION) ) {
				alt153=3;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return res;}
				NoViableAltException nvae =
					new NoViableAltException("", 153, 0, input);
				throw nvae;
			}

			switch (alt153) {
				case 1 :
					// Parser.g:1139:7: K_ALL K_FUNCTIONS
					{
					match(input,K_ALL,FOLLOW_K_ALL_in_functionResource7960); if (state.failed) return res;
					match(input,K_FUNCTIONS,FOLLOW_K_FUNCTIONS_in_functionResource7962); if (state.failed) return res;
					if ( state.backtracking==0 ) { res = FunctionResource.root(); }
					}
					break;
				case 2 :
					// Parser.g:1140:7: K_ALL K_FUNCTIONS K_IN K_KEYSPACE ks= keyspaceName
					{
					match(input,K_ALL,FOLLOW_K_ALL_in_functionResource7972); if (state.failed) return res;
					match(input,K_FUNCTIONS,FOLLOW_K_FUNCTIONS_in_functionResource7974); if (state.failed) return res;
					match(input,K_IN,FOLLOW_K_IN_in_functionResource7976); if (state.failed) return res;
					match(input,K_KEYSPACE,FOLLOW_K_KEYSPACE_in_functionResource7978); if (state.failed) return res;
					pushFollow(FOLLOW_keyspaceName_in_functionResource7984);
					ks=keyspaceName();
					state._fsp--;
					if (state.failed) return res;
					if ( state.backtracking==0 ) { res = FunctionResource.keyspace(ks); }
					}
					break;
				case 3 :
					// Parser.g:1142:7: K_FUNCTION fn= functionName ( '(' (v= comparatorType ( ',' v= comparatorType )* )? ')' )
					{
					match(input,K_FUNCTION,FOLLOW_K_FUNCTION_in_functionResource7999); if (state.failed) return res;
					pushFollow(FOLLOW_functionName_in_functionResource8003);
					fn=functionName();
					state._fsp--;
					if (state.failed) return res;
					// Parser.g:1143:7: ( '(' (v= comparatorType ( ',' v= comparatorType )* )? ')' )
					// Parser.g:1144:9: '(' (v= comparatorType ( ',' v= comparatorType )* )? ')'
					{
					match(input,190,FOLLOW_190_in_functionResource8021); if (state.failed) return res;
					// Parser.g:1145:11: (v= comparatorType ( ',' v= comparatorType )* )?
					int alt152=2;
					int LA152_0 = input.LA(1);
					if ( (LA152_0==IDENT||(LA152_0 >= K_AGGREGATE && LA152_0 <= K_ALL)||LA152_0==K_AS||LA152_0==K_ASCII||(LA152_0 >= K_BIGINT && LA152_0 <= K_BOOLEAN)||(LA152_0 >= K_CALLED && LA152_0 <= K_CLUSTERING)||(LA152_0 >= K_COMPACT && LA152_0 <= K_COUNTER)||LA152_0==K_CUSTOM||(LA152_0 >= K_DATE && LA152_0 <= K_DECIMAL)||(LA152_0 >= K_DISTINCT && LA152_0 <= K_DOUBLE)||LA152_0==K_DURATION||(LA152_0 >= K_EXISTS && LA152_0 <= K_FLOAT)||LA152_0==K_FROZEN||(LA152_0 >= K_FUNCTION && LA152_0 <= K_FUNCTIONS)||LA152_0==K_GROUP||(LA152_0 >= K_INET && LA152_0 <= K_INPUT)||LA152_0==K_INT||(LA152_0 >= K_JSON && LA152_0 <= K_KEYS)||(LA152_0 >= K_KEYSPACES && LA152_0 <= K_LIKE)||(LA152_0 >= K_LIST && LA152_0 <= K_MAP)||LA152_0==K_NOLOGIN||LA152_0==K_NOSUPERUSER||LA152_0==K_OPTIONS||(LA152_0 >= K_PARTITION && LA152_0 <= K_PERMISSIONS)||LA152_0==K_RETURNS||(LA152_0 >= K_ROLE && LA152_0 <= K_ROLES)||(LA152_0 >= K_SET && LA152_0 <= K_TINYINT)||LA152_0==K_TRIGGER||(LA152_0 >= K_TTL && LA152_0 <= K_TYPE)||(LA152_0 >= K_USER && LA152_0 <= K_USERS)||(LA152_0 >= K_UUID && LA152_0 <= K_VARINT)||LA152_0==K_WRITETIME||LA152_0==QUOTED_NAME||LA152_0==STRING_LITERAL) ) {
						alt152=1;
					}
					switch (alt152) {
						case 1 :
							// Parser.g:1146:13: v= comparatorType ( ',' v= comparatorType )*
							{
							pushFollow(FOLLOW_comparatorType_in_functionResource8049);
							v=comparatorType();
							state._fsp--;
							if (state.failed) return res;
							if ( state.backtracking==0 ) { argsTypes.add(v); }
							// Parser.g:1147:13: ( ',' v= comparatorType )*
							loop151:
							while (true) {
								int alt151=2;
								int LA151_0 = input.LA(1);
								if ( (LA151_0==194) ) {
									alt151=1;
								}

								switch (alt151) {
								case 1 :
									// Parser.g:1147:15: ',' v= comparatorType
									{
									match(input,194,FOLLOW_194_in_functionResource8067); if (state.failed) return res;
									pushFollow(FOLLOW_comparatorType_in_functionResource8071);
									v=comparatorType();
									state._fsp--;
									if (state.failed) return res;
									if ( state.backtracking==0 ) { argsTypes.add(v); }
									}
									break;

								default :
									break loop151;
								}
							}

							}
							break;

					}

					match(input,191,FOLLOW_191_in_functionResource8099); if (state.failed) return res;
					}

					if ( state.backtracking==0 ) { res = FunctionResource.functionFromCql(fn.keyspace, fn.name, argsTypes); }
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return res;
	}
	// $ANTLR end "functionResource"



	// $ANTLR start "createUserStatement"
	// Parser.g:1157:1: createUserStatement returns [CreateRoleStatement stmt] : K_CREATE K_USER ( K_IF K_NOT K_EXISTS )? u= username ( K_WITH userPassword[opts] )? ( K_SUPERUSER | K_NOSUPERUSER )? ;
	public final CreateRoleStatement createUserStatement() throws RecognitionException {
		CreateRoleStatement stmt = null;


		ParserRuleReturnScope u =null;


		        RoleOptions opts = new RoleOptions();
		        opts.setOption(IRoleManager.Option.LOGIN, true);
		        boolean superuser = false;
		        boolean ifNotExists = false;
		        RoleName name = new RoleName();
		    
		try {
			// Parser.g:1165:5: ( K_CREATE K_USER ( K_IF K_NOT K_EXISTS )? u= username ( K_WITH userPassword[opts] )? ( K_SUPERUSER | K_NOSUPERUSER )? )
			// Parser.g:1165:7: K_CREATE K_USER ( K_IF K_NOT K_EXISTS )? u= username ( K_WITH userPassword[opts] )? ( K_SUPERUSER | K_NOSUPERUSER )?
			{
			match(input,K_CREATE,FOLLOW_K_CREATE_in_createUserStatement8147); if (state.failed) return stmt;
			match(input,K_USER,FOLLOW_K_USER_in_createUserStatement8149); if (state.failed) return stmt;
			// Parser.g:1165:23: ( K_IF K_NOT K_EXISTS )?
			int alt154=2;
			int LA154_0 = input.LA(1);
			if ( (LA154_0==K_IF) ) {
				alt154=1;
			}
			switch (alt154) {
				case 1 :
					// Parser.g:1165:24: K_IF K_NOT K_EXISTS
					{
					match(input,K_IF,FOLLOW_K_IF_in_createUserStatement8152); if (state.failed) return stmt;
					match(input,K_NOT,FOLLOW_K_NOT_in_createUserStatement8154); if (state.failed) return stmt;
					match(input,K_EXISTS,FOLLOW_K_EXISTS_in_createUserStatement8156); if (state.failed) return stmt;
					if ( state.backtracking==0 ) { ifNotExists = true; }
					}
					break;

			}

			pushFollow(FOLLOW_username_in_createUserStatement8164);
			u=username();
			state._fsp--;
			if (state.failed) return stmt;
			if ( state.backtracking==0 ) { name.setName((u!=null?input.toString(u.start,u.stop):null), true); }
			// Parser.g:1166:7: ( K_WITH userPassword[opts] )?
			int alt155=2;
			int LA155_0 = input.LA(1);
			if ( (LA155_0==K_WITH) ) {
				alt155=1;
			}
			switch (alt155) {
				case 1 :
					// Parser.g:1166:9: K_WITH userPassword[opts]
					{
					match(input,K_WITH,FOLLOW_K_WITH_in_createUserStatement8176); if (state.failed) return stmt;
					pushFollow(FOLLOW_userPassword_in_createUserStatement8178);
					userPassword(opts);
					state._fsp--;
					if (state.failed) return stmt;
					}
					break;

			}

			// Parser.g:1167:7: ( K_SUPERUSER | K_NOSUPERUSER )?
			int alt156=3;
			int LA156_0 = input.LA(1);
			if ( (LA156_0==K_SUPERUSER) ) {
				alt156=1;
			}
			else if ( (LA156_0==K_NOSUPERUSER) ) {
				alt156=2;
			}
			switch (alt156) {
				case 1 :
					// Parser.g:1167:9: K_SUPERUSER
					{
					match(input,K_SUPERUSER,FOLLOW_K_SUPERUSER_in_createUserStatement8192); if (state.failed) return stmt;
					if ( state.backtracking==0 ) { superuser = true; }
					}
					break;
				case 2 :
					// Parser.g:1167:45: K_NOSUPERUSER
					{
					match(input,K_NOSUPERUSER,FOLLOW_K_NOSUPERUSER_in_createUserStatement8198); if (state.failed) return stmt;
					if ( state.backtracking==0 ) { superuser = false; }
					}
					break;

			}

			if ( state.backtracking==0 ) { opts.setOption(IRoleManager.Option.SUPERUSER, superuser);
			        stmt = new CreateRoleStatement(name, opts, DCPermissions.all(), ifNotExists); }
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return stmt;
	}
	// $ANTLR end "createUserStatement"



	// $ANTLR start "alterUserStatement"
	// Parser.g:1175:1: alterUserStatement returns [AlterRoleStatement stmt] : K_ALTER K_USER u= username ( K_WITH userPassword[opts] )? ( K_SUPERUSER | K_NOSUPERUSER )? ;
	public final AlterRoleStatement alterUserStatement() throws RecognitionException {
		AlterRoleStatement stmt = null;


		ParserRuleReturnScope u =null;


		        RoleOptions opts = new RoleOptions();
		        RoleName name = new RoleName();
		    
		try {
			// Parser.g:1180:5: ( K_ALTER K_USER u= username ( K_WITH userPassword[opts] )? ( K_SUPERUSER | K_NOSUPERUSER )? )
			// Parser.g:1180:7: K_ALTER K_USER u= username ( K_WITH userPassword[opts] )? ( K_SUPERUSER | K_NOSUPERUSER )?
			{
			match(input,K_ALTER,FOLLOW_K_ALTER_in_alterUserStatement8243); if (state.failed) return stmt;
			match(input,K_USER,FOLLOW_K_USER_in_alterUserStatement8245); if (state.failed) return stmt;
			pushFollow(FOLLOW_username_in_alterUserStatement8249);
			u=username();
			state._fsp--;
			if (state.failed) return stmt;
			if ( state.backtracking==0 ) { name.setName((u!=null?input.toString(u.start,u.stop):null), true); }
			// Parser.g:1181:7: ( K_WITH userPassword[opts] )?
			int alt157=2;
			int LA157_0 = input.LA(1);
			if ( (LA157_0==K_WITH) ) {
				alt157=1;
			}
			switch (alt157) {
				case 1 :
					// Parser.g:1181:9: K_WITH userPassword[opts]
					{
					match(input,K_WITH,FOLLOW_K_WITH_in_alterUserStatement8261); if (state.failed) return stmt;
					pushFollow(FOLLOW_userPassword_in_alterUserStatement8263);
					userPassword(opts);
					state._fsp--;
					if (state.failed) return stmt;
					}
					break;

			}

			// Parser.g:1182:7: ( K_SUPERUSER | K_NOSUPERUSER )?
			int alt158=3;
			int LA158_0 = input.LA(1);
			if ( (LA158_0==K_SUPERUSER) ) {
				alt158=1;
			}
			else if ( (LA158_0==K_NOSUPERUSER) ) {
				alt158=2;
			}
			switch (alt158) {
				case 1 :
					// Parser.g:1182:9: K_SUPERUSER
					{
					match(input,K_SUPERUSER,FOLLOW_K_SUPERUSER_in_alterUserStatement8277); if (state.failed) return stmt;
					if ( state.backtracking==0 ) { opts.setOption(IRoleManager.Option.SUPERUSER, true); }
					}
					break;
				case 2 :
					// Parser.g:1183:11: K_NOSUPERUSER
					{
					match(input,K_NOSUPERUSER,FOLLOW_K_NOSUPERUSER_in_alterUserStatement8291); if (state.failed) return stmt;
					if ( state.backtracking==0 ) { opts.setOption(IRoleManager.Option.SUPERUSER, false); }
					}
					break;

			}

			if ( state.backtracking==0 ) {  stmt = new AlterRoleStatement(name, opts, null); }
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return stmt;
	}
	// $ANTLR end "alterUserStatement"



	// $ANTLR start "dropUserStatement"
	// Parser.g:1190:1: dropUserStatement returns [DropRoleStatement stmt] : K_DROP K_USER ( K_IF K_EXISTS )? u= username ;
	public final DropRoleStatement dropUserStatement() throws RecognitionException {
		DropRoleStatement stmt = null;


		ParserRuleReturnScope u =null;


		        boolean ifExists = false;
		        RoleName name = new RoleName();
		    
		try {
			// Parser.g:1195:5: ( K_DROP K_USER ( K_IF K_EXISTS )? u= username )
			// Parser.g:1195:7: K_DROP K_USER ( K_IF K_EXISTS )? u= username
			{
			match(input,K_DROP,FOLLOW_K_DROP_in_dropUserStatement8337); if (state.failed) return stmt;
			match(input,K_USER,FOLLOW_K_USER_in_dropUserStatement8339); if (state.failed) return stmt;
			// Parser.g:1195:21: ( K_IF K_EXISTS )?
			int alt159=2;
			int LA159_0 = input.LA(1);
			if ( (LA159_0==K_IF) ) {
				alt159=1;
			}
			switch (alt159) {
				case 1 :
					// Parser.g:1195:22: K_IF K_EXISTS
					{
					match(input,K_IF,FOLLOW_K_IF_in_dropUserStatement8342); if (state.failed) return stmt;
					match(input,K_EXISTS,FOLLOW_K_EXISTS_in_dropUserStatement8344); if (state.failed) return stmt;
					if ( state.backtracking==0 ) { ifExists = true; }
					}
					break;

			}

			pushFollow(FOLLOW_username_in_dropUserStatement8352);
			u=username();
			state._fsp--;
			if (state.failed) return stmt;
			if ( state.backtracking==0 ) { name.setName((u!=null?input.toString(u.start,u.stop):null), true); stmt = new DropRoleStatement(name, ifExists); }
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return stmt;
	}
	// $ANTLR end "dropUserStatement"



	// $ANTLR start "listUsersStatement"
	// Parser.g:1201:1: listUsersStatement returns [ListRolesStatement stmt] : K_LIST K_USERS ;
	public final ListRolesStatement listUsersStatement() throws RecognitionException {
		ListRolesStatement stmt = null;


		try {
			// Parser.g:1202:5: ( K_LIST K_USERS )
			// Parser.g:1202:7: K_LIST K_USERS
			{
			match(input,K_LIST,FOLLOW_K_LIST_in_listUsersStatement8377); if (state.failed) return stmt;
			match(input,K_USERS,FOLLOW_K_USERS_in_listUsersStatement8379); if (state.failed) return stmt;
			if ( state.backtracking==0 ) { stmt = new ListUsersStatement(); }
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return stmt;
	}
	// $ANTLR end "listUsersStatement"



	// $ANTLR start "createRoleStatement"
	// Parser.g:1214:1: createRoleStatement returns [CreateRoleStatement stmt] : K_CREATE K_ROLE ( K_IF K_NOT K_EXISTS )? name= userOrRoleName ( K_WITH roleOptions[opts, dcperms] )? ;
	public final CreateRoleStatement createRoleStatement() throws RecognitionException {
		CreateRoleStatement stmt = null;


		RoleName name =null;


		        RoleOptions opts = new RoleOptions();
		        DCPermissions.Builder dcperms = DCPermissions.builder();
		        boolean ifNotExists = false;
		    
		try {
			// Parser.g:1220:5: ( K_CREATE K_ROLE ( K_IF K_NOT K_EXISTS )? name= userOrRoleName ( K_WITH roleOptions[opts, dcperms] )? )
			// Parser.g:1220:7: K_CREATE K_ROLE ( K_IF K_NOT K_EXISTS )? name= userOrRoleName ( K_WITH roleOptions[opts, dcperms] )?
			{
			match(input,K_CREATE,FOLLOW_K_CREATE_in_createRoleStatement8413); if (state.failed) return stmt;
			match(input,K_ROLE,FOLLOW_K_ROLE_in_createRoleStatement8415); if (state.failed) return stmt;
			// Parser.g:1220:23: ( K_IF K_NOT K_EXISTS )?
			int alt160=2;
			int LA160_0 = input.LA(1);
			if ( (LA160_0==K_IF) ) {
				alt160=1;
			}
			switch (alt160) {
				case 1 :
					// Parser.g:1220:24: K_IF K_NOT K_EXISTS
					{
					match(input,K_IF,FOLLOW_K_IF_in_createRoleStatement8418); if (state.failed) return stmt;
					match(input,K_NOT,FOLLOW_K_NOT_in_createRoleStatement8420); if (state.failed) return stmt;
					match(input,K_EXISTS,FOLLOW_K_EXISTS_in_createRoleStatement8422); if (state.failed) return stmt;
					if ( state.backtracking==0 ) { ifNotExists = true; }
					}
					break;

			}

			pushFollow(FOLLOW_userOrRoleName_in_createRoleStatement8430);
			name=userOrRoleName();
			state._fsp--;
			if (state.failed) return stmt;
			// Parser.g:1221:7: ( K_WITH roleOptions[opts, dcperms] )?
			int alt161=2;
			int LA161_0 = input.LA(1);
			if ( (LA161_0==K_WITH) ) {
				alt161=1;
			}
			switch (alt161) {
				case 1 :
					// Parser.g:1221:9: K_WITH roleOptions[opts, dcperms]
					{
					match(input,K_WITH,FOLLOW_K_WITH_in_createRoleStatement8440); if (state.failed) return stmt;
					pushFollow(FOLLOW_roleOptions_in_createRoleStatement8442);
					roleOptions(opts, dcperms);
					state._fsp--;
					if (state.failed) return stmt;
					}
					break;

			}

			if ( state.backtracking==0 ) {
			        // set defaults if they weren't explictly supplied
			        if (!opts.getLogin().isPresent())
			        {
			            opts.setOption(IRoleManager.Option.LOGIN, false);
			        }
			        if (!opts.getSuperuser().isPresent())
			        {
			            opts.setOption(IRoleManager.Option.SUPERUSER, false);
			        }
			        stmt = new CreateRoleStatement(name, opts, dcperms.build(), ifNotExists);
			      }
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return stmt;
	}
	// $ANTLR end "createRoleStatement"



	// $ANTLR start "alterRoleStatement"
	// Parser.g:1245:1: alterRoleStatement returns [AlterRoleStatement stmt] : K_ALTER K_ROLE name= userOrRoleName ( K_WITH roleOptions[opts, dcperms] )? ;
	public final AlterRoleStatement alterRoleStatement() throws RecognitionException {
		AlterRoleStatement stmt = null;


		RoleName name =null;


		        RoleOptions opts = new RoleOptions();
		        DCPermissions.Builder dcperms = DCPermissions.builder();
		    
		try {
			// Parser.g:1250:5: ( K_ALTER K_ROLE name= userOrRoleName ( K_WITH roleOptions[opts, dcperms] )? )
			// Parser.g:1250:7: K_ALTER K_ROLE name= userOrRoleName ( K_WITH roleOptions[opts, dcperms] )?
			{
			match(input,K_ALTER,FOLLOW_K_ALTER_in_alterRoleStatement8486); if (state.failed) return stmt;
			match(input,K_ROLE,FOLLOW_K_ROLE_in_alterRoleStatement8488); if (state.failed) return stmt;
			pushFollow(FOLLOW_userOrRoleName_in_alterRoleStatement8492);
			name=userOrRoleName();
			state._fsp--;
			if (state.failed) return stmt;
			// Parser.g:1251:7: ( K_WITH roleOptions[opts, dcperms] )?
			int alt162=2;
			int LA162_0 = input.LA(1);
			if ( (LA162_0==K_WITH) ) {
				alt162=1;
			}
			switch (alt162) {
				case 1 :
					// Parser.g:1251:9: K_WITH roleOptions[opts, dcperms]
					{
					match(input,K_WITH,FOLLOW_K_WITH_in_alterRoleStatement8502); if (state.failed) return stmt;
					pushFollow(FOLLOW_roleOptions_in_alterRoleStatement8504);
					roleOptions(opts, dcperms);
					state._fsp--;
					if (state.failed) return stmt;
					}
					break;

			}

			if ( state.backtracking==0 ) {  stmt = new AlterRoleStatement(name, opts, dcperms.isModified() ? dcperms.build() : null); }
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return stmt;
	}
	// $ANTLR end "alterRoleStatement"



	// $ANTLR start "dropRoleStatement"
	// Parser.g:1258:1: dropRoleStatement returns [DropRoleStatement stmt] : K_DROP K_ROLE ( K_IF K_EXISTS )? name= userOrRoleName ;
	public final DropRoleStatement dropRoleStatement() throws RecognitionException {
		DropRoleStatement stmt = null;


		RoleName name =null;


		        boolean ifExists = false;
		    
		try {
			// Parser.g:1262:5: ( K_DROP K_ROLE ( K_IF K_EXISTS )? name= userOrRoleName )
			// Parser.g:1262:7: K_DROP K_ROLE ( K_IF K_EXISTS )? name= userOrRoleName
			{
			match(input,K_DROP,FOLLOW_K_DROP_in_dropRoleStatement8548); if (state.failed) return stmt;
			match(input,K_ROLE,FOLLOW_K_ROLE_in_dropRoleStatement8550); if (state.failed) return stmt;
			// Parser.g:1262:21: ( K_IF K_EXISTS )?
			int alt163=2;
			int LA163_0 = input.LA(1);
			if ( (LA163_0==K_IF) ) {
				alt163=1;
			}
			switch (alt163) {
				case 1 :
					// Parser.g:1262:22: K_IF K_EXISTS
					{
					match(input,K_IF,FOLLOW_K_IF_in_dropRoleStatement8553); if (state.failed) return stmt;
					match(input,K_EXISTS,FOLLOW_K_EXISTS_in_dropRoleStatement8555); if (state.failed) return stmt;
					if ( state.backtracking==0 ) { ifExists = true; }
					}
					break;

			}

			pushFollow(FOLLOW_userOrRoleName_in_dropRoleStatement8563);
			name=userOrRoleName();
			state._fsp--;
			if (state.failed) return stmt;
			if ( state.backtracking==0 ) { stmt = new DropRoleStatement(name, ifExists); }
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return stmt;
	}
	// $ANTLR end "dropRoleStatement"



	// $ANTLR start "listRolesStatement"
	// Parser.g:1269:1: listRolesStatement returns [ListRolesStatement stmt] : K_LIST K_ROLES ( K_OF roleName[grantee] )? ( K_NORECURSIVE )? ;
	public final ListRolesStatement listRolesStatement() throws RecognitionException {
		ListRolesStatement stmt = null;



		        boolean recursive = true;
		        RoleName grantee = new RoleName();
		    
		try {
			// Parser.g:1274:5: ( K_LIST K_ROLES ( K_OF roleName[grantee] )? ( K_NORECURSIVE )? )
			// Parser.g:1274:7: K_LIST K_ROLES ( K_OF roleName[grantee] )? ( K_NORECURSIVE )?
			{
			match(input,K_LIST,FOLLOW_K_LIST_in_listRolesStatement8603); if (state.failed) return stmt;
			match(input,K_ROLES,FOLLOW_K_ROLES_in_listRolesStatement8605); if (state.failed) return stmt;
			// Parser.g:1275:7: ( K_OF roleName[grantee] )?
			int alt164=2;
			int LA164_0 = input.LA(1);
			if ( (LA164_0==K_OF) ) {
				alt164=1;
			}
			switch (alt164) {
				case 1 :
					// Parser.g:1275:9: K_OF roleName[grantee]
					{
					match(input,K_OF,FOLLOW_K_OF_in_listRolesStatement8615); if (state.failed) return stmt;
					pushFollow(FOLLOW_roleName_in_listRolesStatement8617);
					roleName(grantee);
					state._fsp--;
					if (state.failed) return stmt;
					}
					break;

			}

			// Parser.g:1276:7: ( K_NORECURSIVE )?
			int alt165=2;
			int LA165_0 = input.LA(1);
			if ( (LA165_0==K_NORECURSIVE) ) {
				alt165=1;
			}
			switch (alt165) {
				case 1 :
					// Parser.g:1276:9: K_NORECURSIVE
					{
					match(input,K_NORECURSIVE,FOLLOW_K_NORECURSIVE_in_listRolesStatement8630); if (state.failed) return stmt;
					if ( state.backtracking==0 ) { recursive = false; }
					}
					break;

			}

			if ( state.backtracking==0 ) { stmt = new ListRolesStatement(grantee, recursive); }
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return stmt;
	}
	// $ANTLR end "listRolesStatement"



	// $ANTLR start "roleOptions"
	// Parser.g:1280:1: roleOptions[RoleOptions opts, DCPermissions.Builder dcperms] : roleOption[opts, dcperms] ( K_AND roleOption[opts, dcperms] )* ;
	public final void roleOptions(RoleOptions opts, DCPermissions.Builder dcperms) throws RecognitionException {
		try {
			// Parser.g:1281:5: ( roleOption[opts, dcperms] ( K_AND roleOption[opts, dcperms] )* )
			// Parser.g:1281:7: roleOption[opts, dcperms] ( K_AND roleOption[opts, dcperms] )*
			{
			pushFollow(FOLLOW_roleOption_in_roleOptions8661);
			roleOption(opts, dcperms);
			state._fsp--;
			if (state.failed) return;
			// Parser.g:1281:33: ( K_AND roleOption[opts, dcperms] )*
			loop166:
			while (true) {
				int alt166=2;
				int LA166_0 = input.LA(1);
				if ( (LA166_0==K_AND) ) {
					alt166=1;
				}

				switch (alt166) {
				case 1 :
					// Parser.g:1281:34: K_AND roleOption[opts, dcperms]
					{
					match(input,K_AND,FOLLOW_K_AND_in_roleOptions8665); if (state.failed) return;
					pushFollow(FOLLOW_roleOption_in_roleOptions8667);
					roleOption(opts, dcperms);
					state._fsp--;
					if (state.failed) return;
					}
					break;

				default :
					break loop166;
				}
			}

			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "roleOptions"



	// $ANTLR start "roleOption"
	// Parser.g:1284:1: roleOption[RoleOptions opts, DCPermissions.Builder dcperms] : ( K_PASSWORD '=' v= STRING_LITERAL | K_OPTIONS '=' m= fullMapLiteral | K_SUPERUSER '=' b= BOOLEAN | K_LOGIN '=' b= BOOLEAN | K_ACCESS K_TO K_ALL K_DATACENTERS | K_ACCESS K_TO K_DATACENTERS '{' dcPermission[dcperms] ( ',' dcPermission[dcperms] )* '}' );
	public final void roleOption(RoleOptions opts, DCPermissions.Builder dcperms) throws RecognitionException {
		Token v=null;
		Token b=null;
		Maps.Literal m =null;

		try {
			// Parser.g:1285:5: ( K_PASSWORD '=' v= STRING_LITERAL | K_OPTIONS '=' m= fullMapLiteral | K_SUPERUSER '=' b= BOOLEAN | K_LOGIN '=' b= BOOLEAN | K_ACCESS K_TO K_ALL K_DATACENTERS | K_ACCESS K_TO K_DATACENTERS '{' dcPermission[dcperms] ( ',' dcPermission[dcperms] )* '}' )
			int alt168=6;
			switch ( input.LA(1) ) {
			case K_PASSWORD:
				{
				alt168=1;
				}
				break;
			case K_OPTIONS:
				{
				alt168=2;
				}
				break;
			case K_SUPERUSER:
				{
				alt168=3;
				}
				break;
			case K_LOGIN:
				{
				alt168=4;
				}
				break;
			case K_ACCESS:
				{
				int LA168_5 = input.LA(2);
				if ( (LA168_5==K_TO) ) {
					int LA168_6 = input.LA(3);
					if ( (LA168_6==K_ALL) ) {
						alt168=5;
					}
					else if ( (LA168_6==K_DATACENTERS) ) {
						alt168=6;
					}

					else {
						if (state.backtracking>0) {state.failed=true; return;}
						int nvaeMark = input.mark();
						try {
							for (int nvaeConsume = 0; nvaeConsume < 3 - 1; nvaeConsume++) {
								input.consume();
							}
							NoViableAltException nvae =
								new NoViableAltException("", 168, 6, input);
							throw nvae;
						} finally {
							input.rewind(nvaeMark);
						}
					}

				}

				else {
					if (state.backtracking>0) {state.failed=true; return;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 168, 5, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return;}
				NoViableAltException nvae =
					new NoViableAltException("", 168, 0, input);
				throw nvae;
			}
			switch (alt168) {
				case 1 :
					// Parser.g:1285:8: K_PASSWORD '=' v= STRING_LITERAL
					{
					match(input,K_PASSWORD,FOLLOW_K_PASSWORD_in_roleOption8689); if (state.failed) return;
					match(input,203,FOLLOW_203_in_roleOption8691); if (state.failed) return;
					v=(Token)match(input,STRING_LITERAL,FOLLOW_STRING_LITERAL_in_roleOption8695); if (state.failed) return;
					if ( state.backtracking==0 ) { opts.setOption(IRoleManager.Option.PASSWORD, (v!=null?v.getText():null)); }
					}
					break;
				case 2 :
					// Parser.g:1286:8: K_OPTIONS '=' m= fullMapLiteral
					{
					match(input,K_OPTIONS,FOLLOW_K_OPTIONS_in_roleOption8706); if (state.failed) return;
					match(input,203,FOLLOW_203_in_roleOption8708); if (state.failed) return;
					pushFollow(FOLLOW_fullMapLiteral_in_roleOption8712);
					m=fullMapLiteral();
					state._fsp--;
					if (state.failed) return;
					if ( state.backtracking==0 ) { opts.setOption(IRoleManager.Option.OPTIONS, convertPropertyMap(m)); }
					}
					break;
				case 3 :
					// Parser.g:1287:8: K_SUPERUSER '=' b= BOOLEAN
					{
					match(input,K_SUPERUSER,FOLLOW_K_SUPERUSER_in_roleOption8723); if (state.failed) return;
					match(input,203,FOLLOW_203_in_roleOption8725); if (state.failed) return;
					b=(Token)match(input,BOOLEAN,FOLLOW_BOOLEAN_in_roleOption8729); if (state.failed) return;
					if ( state.backtracking==0 ) { opts.setOption(IRoleManager.Option.SUPERUSER, Boolean.valueOf((b!=null?b.getText():null))); }
					}
					break;
				case 4 :
					// Parser.g:1288:8: K_LOGIN '=' b= BOOLEAN
					{
					match(input,K_LOGIN,FOLLOW_K_LOGIN_in_roleOption8740); if (state.failed) return;
					match(input,203,FOLLOW_203_in_roleOption8742); if (state.failed) return;
					b=(Token)match(input,BOOLEAN,FOLLOW_BOOLEAN_in_roleOption8746); if (state.failed) return;
					if ( state.backtracking==0 ) { opts.setOption(IRoleManager.Option.LOGIN, Boolean.valueOf((b!=null?b.getText():null))); }
					}
					break;
				case 5 :
					// Parser.g:1289:8: K_ACCESS K_TO K_ALL K_DATACENTERS
					{
					match(input,K_ACCESS,FOLLOW_K_ACCESS_in_roleOption8757); if (state.failed) return;
					match(input,K_TO,FOLLOW_K_TO_in_roleOption8759); if (state.failed) return;
					match(input,K_ALL,FOLLOW_K_ALL_in_roleOption8761); if (state.failed) return;
					match(input,K_DATACENTERS,FOLLOW_K_DATACENTERS_in_roleOption8763); if (state.failed) return;
					if ( state.backtracking==0 ) { dcperms.all(); }
					}
					break;
				case 6 :
					// Parser.g:1290:8: K_ACCESS K_TO K_DATACENTERS '{' dcPermission[dcperms] ( ',' dcPermission[dcperms] )* '}'
					{
					match(input,K_ACCESS,FOLLOW_K_ACCESS_in_roleOption8774); if (state.failed) return;
					match(input,K_TO,FOLLOW_K_TO_in_roleOption8776); if (state.failed) return;
					match(input,K_DATACENTERS,FOLLOW_K_DATACENTERS_in_roleOption8778); if (state.failed) return;
					match(input,210,FOLLOW_210_in_roleOption8780); if (state.failed) return;
					pushFollow(FOLLOW_dcPermission_in_roleOption8782);
					dcPermission(dcperms);
					state._fsp--;
					if (state.failed) return;
					// Parser.g:1290:62: ( ',' dcPermission[dcperms] )*
					loop167:
					while (true) {
						int alt167=2;
						int LA167_0 = input.LA(1);
						if ( (LA167_0==194) ) {
							alt167=1;
						}

						switch (alt167) {
						case 1 :
							// Parser.g:1290:63: ',' dcPermission[dcperms]
							{
							match(input,194,FOLLOW_194_in_roleOption8786); if (state.failed) return;
							pushFollow(FOLLOW_dcPermission_in_roleOption8788);
							dcPermission(dcperms);
							state._fsp--;
							if (state.failed) return;
							}
							break;

						default :
							break loop167;
						}
					}

					match(input,211,FOLLOW_211_in_roleOption8793); if (state.failed) return;
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "roleOption"



	// $ANTLR start "dcPermission"
	// Parser.g:1293:1: dcPermission[DCPermissions.Builder builder] : dc= STRING_LITERAL ;
	public final void dcPermission(DCPermissions.Builder builder) throws RecognitionException {
		Token dc=null;

		try {
			// Parser.g:1294:5: (dc= STRING_LITERAL )
			// Parser.g:1294:7: dc= STRING_LITERAL
			{
			dc=(Token)match(input,STRING_LITERAL,FOLLOW_STRING_LITERAL_in_dcPermission8813); if (state.failed) return;
			if ( state.backtracking==0 ) { builder.add((dc!=null?dc.getText():null)); }
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "dcPermission"



	// $ANTLR start "userPassword"
	// Parser.g:1298:1: userPassword[RoleOptions opts] : K_PASSWORD v= STRING_LITERAL ;
	public final void userPassword(RoleOptions opts) throws RecognitionException {
		Token v=null;

		try {
			// Parser.g:1299:5: ( K_PASSWORD v= STRING_LITERAL )
			// Parser.g:1299:8: K_PASSWORD v= STRING_LITERAL
			{
			match(input,K_PASSWORD,FOLLOW_K_PASSWORD_in_userPassword8835); if (state.failed) return;
			v=(Token)match(input,STRING_LITERAL,FOLLOW_STRING_LITERAL_in_userPassword8839); if (state.failed) return;
			if ( state.backtracking==0 ) { opts.setOption(IRoleManager.Option.PASSWORD, (v!=null?v.getText():null)); }
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "userPassword"



	// $ANTLR start "cident"
	// Parser.g:1310:1: cident returns [ColumnMetadata.Raw id] : ( EMPTY_QUOTED_NAME |t= IDENT |t= QUOTED_NAME |k= unreserved_keyword );
	public final ColumnMetadata.Raw cident() throws RecognitionException {
		ColumnMetadata.Raw id = null;


		Token t=null;
		String k =null;

		try {
			// Parser.g:1311:5: ( EMPTY_QUOTED_NAME |t= IDENT |t= QUOTED_NAME |k= unreserved_keyword )
			int alt169=4;
			switch ( input.LA(1) ) {
			case EMPTY_QUOTED_NAME:
				{
				alt169=1;
				}
				break;
			case IDENT:
				{
				alt169=2;
				}
				break;
			case QUOTED_NAME:
				{
				alt169=3;
				}
				break;
			case K_AGGREGATE:
			case K_ALL:
			case K_AS:
			case K_ASCII:
			case K_BIGINT:
			case K_BLOB:
			case K_BOOLEAN:
			case K_CALLED:
			case K_CAST:
			case K_CLUSTERING:
			case K_COMPACT:
			case K_CONTAINS:
			case K_COUNT:
			case K_COUNTER:
			case K_CUSTOM:
			case K_DATE:
			case K_DECIMAL:
			case K_DISTINCT:
			case K_DOUBLE:
			case K_DURATION:
			case K_EXISTS:
			case K_FILTERING:
			case K_FINALFUNC:
			case K_FLOAT:
			case K_FROZEN:
			case K_FUNCTION:
			case K_FUNCTIONS:
			case K_GROUP:
			case K_INET:
			case K_INITCOND:
			case K_INPUT:
			case K_INT:
			case K_JSON:
			case K_KEY:
			case K_KEYS:
			case K_KEYSPACES:
			case K_LANGUAGE:
			case K_LIKE:
			case K_LIST:
			case K_LOGIN:
			case K_MAP:
			case K_NOLOGIN:
			case K_NOSUPERUSER:
			case K_OPTIONS:
			case K_PARTITION:
			case K_PASSWORD:
			case K_PER:
			case K_PERMISSION:
			case K_PERMISSIONS:
			case K_RETURNS:
			case K_ROLE:
			case K_ROLES:
			case K_SFUNC:
			case K_SMALLINT:
			case K_STATIC:
			case K_STORAGE:
			case K_STYPE:
			case K_SUPERUSER:
			case K_TEXT:
			case K_TIME:
			case K_TIMESTAMP:
			case K_TIMEUUID:
			case K_TINYINT:
			case K_TRIGGER:
			case K_TTL:
			case K_TUPLE:
			case K_TYPE:
			case K_USER:
			case K_USERS:
			case K_UUID:
			case K_VALUES:
			case K_VARCHAR:
			case K_VARINT:
			case K_WRITETIME:
				{
				alt169=4;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return id;}
				NoViableAltException nvae =
					new NoViableAltException("", 169, 0, input);
				throw nvae;
			}
			switch (alt169) {
				case 1 :
					// Parser.g:1311:7: EMPTY_QUOTED_NAME
					{
					match(input,EMPTY_QUOTED_NAME,FOLLOW_EMPTY_QUOTED_NAME_in_cident8871); if (state.failed) return id;
					if ( state.backtracking==0 ) { id = ColumnMetadata.Raw.forQuoted(""); }
					}
					break;
				case 2 :
					// Parser.g:1312:7: t= IDENT
					{
					t=(Token)match(input,IDENT,FOLLOW_IDENT_in_cident8886); if (state.failed) return id;
					if ( state.backtracking==0 ) { id = ColumnMetadata.Raw.forUnquoted((t!=null?t.getText():null)); }
					}
					break;
				case 3 :
					// Parser.g:1313:7: t= QUOTED_NAME
					{
					t=(Token)match(input,QUOTED_NAME,FOLLOW_QUOTED_NAME_in_cident8911); if (state.failed) return id;
					if ( state.backtracking==0 ) { id = ColumnMetadata.Raw.forQuoted((t!=null?t.getText():null)); }
					}
					break;
				case 4 :
					// Parser.g:1314:7: k= unreserved_keyword
					{
					pushFollow(FOLLOW_unreserved_keyword_in_cident8930);
					k=unreserved_keyword();
					state._fsp--;
					if (state.failed) return id;
					if ( state.backtracking==0 ) { id = ColumnMetadata.Raw.forUnquoted(k); }
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return id;
	}
	// $ANTLR end "cident"



	// $ANTLR start "schema_cident"
	// Parser.g:1317:1: schema_cident returns [ColumnMetadata.Raw id] : (t= IDENT |t= QUOTED_NAME |k= unreserved_keyword );
	public final ColumnMetadata.Raw schema_cident() throws RecognitionException {
		ColumnMetadata.Raw id = null;


		Token t=null;
		String k =null;

		try {
			// Parser.g:1318:5: (t= IDENT |t= QUOTED_NAME |k= unreserved_keyword )
			int alt170=3;
			switch ( input.LA(1) ) {
			case IDENT:
				{
				alt170=1;
				}
				break;
			case QUOTED_NAME:
				{
				alt170=2;
				}
				break;
			case K_AGGREGATE:
			case K_ALL:
			case K_AS:
			case K_ASCII:
			case K_BIGINT:
			case K_BLOB:
			case K_BOOLEAN:
			case K_CALLED:
			case K_CAST:
			case K_CLUSTERING:
			case K_COMPACT:
			case K_CONTAINS:
			case K_COUNT:
			case K_COUNTER:
			case K_CUSTOM:
			case K_DATE:
			case K_DECIMAL:
			case K_DISTINCT:
			case K_DOUBLE:
			case K_DURATION:
			case K_EXISTS:
			case K_FILTERING:
			case K_FINALFUNC:
			case K_FLOAT:
			case K_FROZEN:
			case K_FUNCTION:
			case K_FUNCTIONS:
			case K_GROUP:
			case K_INET:
			case K_INITCOND:
			case K_INPUT:
			case K_INT:
			case K_JSON:
			case K_KEY:
			case K_KEYS:
			case K_KEYSPACES:
			case K_LANGUAGE:
			case K_LIKE:
			case K_LIST:
			case K_LOGIN:
			case K_MAP:
			case K_NOLOGIN:
			case K_NOSUPERUSER:
			case K_OPTIONS:
			case K_PARTITION:
			case K_PASSWORD:
			case K_PER:
			case K_PERMISSION:
			case K_PERMISSIONS:
			case K_RETURNS:
			case K_ROLE:
			case K_ROLES:
			case K_SFUNC:
			case K_SMALLINT:
			case K_STATIC:
			case K_STORAGE:
			case K_STYPE:
			case K_SUPERUSER:
			case K_TEXT:
			case K_TIME:
			case K_TIMESTAMP:
			case K_TIMEUUID:
			case K_TINYINT:
			case K_TRIGGER:
			case K_TTL:
			case K_TUPLE:
			case K_TYPE:
			case K_USER:
			case K_USERS:
			case K_UUID:
			case K_VALUES:
			case K_VARCHAR:
			case K_VARINT:
			case K_WRITETIME:
				{
				alt170=3;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return id;}
				NoViableAltException nvae =
					new NoViableAltException("", 170, 0, input);
				throw nvae;
			}
			switch (alt170) {
				case 1 :
					// Parser.g:1318:7: t= IDENT
					{
					t=(Token)match(input,IDENT,FOLLOW_IDENT_in_schema_cident8955); if (state.failed) return id;
					if ( state.backtracking==0 ) { id = ColumnMetadata.Raw.forUnquoted((t!=null?t.getText():null)); }
					}
					break;
				case 2 :
					// Parser.g:1319:7: t= QUOTED_NAME
					{
					t=(Token)match(input,QUOTED_NAME,FOLLOW_QUOTED_NAME_in_schema_cident8980); if (state.failed) return id;
					if ( state.backtracking==0 ) { id = ColumnMetadata.Raw.forQuoted((t!=null?t.getText():null)); }
					}
					break;
				case 3 :
					// Parser.g:1320:7: k= unreserved_keyword
					{
					pushFollow(FOLLOW_unreserved_keyword_in_schema_cident8999);
					k=unreserved_keyword();
					state._fsp--;
					if (state.failed) return id;
					if ( state.backtracking==0 ) { id = ColumnMetadata.Raw.forUnquoted(k); }
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return id;
	}
	// $ANTLR end "schema_cident"



	// $ANTLR start "ident"
	// Parser.g:1324:1: ident returns [ColumnIdentifier id] : (t= IDENT |t= QUOTED_NAME |k= unreserved_keyword );
	public final ColumnIdentifier ident() throws RecognitionException {
		ColumnIdentifier id = null;


		Token t=null;
		String k =null;

		try {
			// Parser.g:1325:5: (t= IDENT |t= QUOTED_NAME |k= unreserved_keyword )
			int alt171=3;
			switch ( input.LA(1) ) {
			case IDENT:
				{
				alt171=1;
				}
				break;
			case QUOTED_NAME:
				{
				alt171=2;
				}
				break;
			case K_AGGREGATE:
			case K_ALL:
			case K_AS:
			case K_ASCII:
			case K_BIGINT:
			case K_BLOB:
			case K_BOOLEAN:
			case K_CALLED:
			case K_CAST:
			case K_CLUSTERING:
			case K_COMPACT:
			case K_CONTAINS:
			case K_COUNT:
			case K_COUNTER:
			case K_CUSTOM:
			case K_DATE:
			case K_DECIMAL:
			case K_DISTINCT:
			case K_DOUBLE:
			case K_DURATION:
			case K_EXISTS:
			case K_FILTERING:
			case K_FINALFUNC:
			case K_FLOAT:
			case K_FROZEN:
			case K_FUNCTION:
			case K_FUNCTIONS:
			case K_GROUP:
			case K_INET:
			case K_INITCOND:
			case K_INPUT:
			case K_INT:
			case K_JSON:
			case K_KEY:
			case K_KEYS:
			case K_KEYSPACES:
			case K_LANGUAGE:
			case K_LIKE:
			case K_LIST:
			case K_LOGIN:
			case K_MAP:
			case K_NOLOGIN:
			case K_NOSUPERUSER:
			case K_OPTIONS:
			case K_PARTITION:
			case K_PASSWORD:
			case K_PER:
			case K_PERMISSION:
			case K_PERMISSIONS:
			case K_RETURNS:
			case K_ROLE:
			case K_ROLES:
			case K_SFUNC:
			case K_SMALLINT:
			case K_STATIC:
			case K_STORAGE:
			case K_STYPE:
			case K_SUPERUSER:
			case K_TEXT:
			case K_TIME:
			case K_TIMESTAMP:
			case K_TIMEUUID:
			case K_TINYINT:
			case K_TRIGGER:
			case K_TTL:
			case K_TUPLE:
			case K_TYPE:
			case K_USER:
			case K_USERS:
			case K_UUID:
			case K_VALUES:
			case K_VARCHAR:
			case K_VARINT:
			case K_WRITETIME:
				{
				alt171=3;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return id;}
				NoViableAltException nvae =
					new NoViableAltException("", 171, 0, input);
				throw nvae;
			}
			switch (alt171) {
				case 1 :
					// Parser.g:1325:7: t= IDENT
					{
					t=(Token)match(input,IDENT,FOLLOW_IDENT_in_ident9025); if (state.failed) return id;
					if ( state.backtracking==0 ) { id = ColumnIdentifier.getInterned((t!=null?t.getText():null), false); }
					}
					break;
				case 2 :
					// Parser.g:1326:7: t= QUOTED_NAME
					{
					t=(Token)match(input,QUOTED_NAME,FOLLOW_QUOTED_NAME_in_ident9050); if (state.failed) return id;
					if ( state.backtracking==0 ) { id = ColumnIdentifier.getInterned((t!=null?t.getText():null), true); }
					}
					break;
				case 3 :
					// Parser.g:1327:7: k= unreserved_keyword
					{
					pushFollow(FOLLOW_unreserved_keyword_in_ident9069);
					k=unreserved_keyword();
					state._fsp--;
					if (state.failed) return id;
					if ( state.backtracking==0 ) { id = ColumnIdentifier.getInterned(k, false); }
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return id;
	}
	// $ANTLR end "ident"



	// $ANTLR start "fident"
	// Parser.g:1330:1: fident returns [FieldIdentifier id] : (t= IDENT |t= QUOTED_NAME |k= unreserved_keyword );
	public final FieldIdentifier fident() throws RecognitionException {
		FieldIdentifier id = null;


		Token t=null;
		String k =null;

		try {
			// Parser.g:1331:5: (t= IDENT |t= QUOTED_NAME |k= unreserved_keyword )
			int alt172=3;
			switch ( input.LA(1) ) {
			case IDENT:
				{
				alt172=1;
				}
				break;
			case QUOTED_NAME:
				{
				alt172=2;
				}
				break;
			case K_AGGREGATE:
			case K_ALL:
			case K_AS:
			case K_ASCII:
			case K_BIGINT:
			case K_BLOB:
			case K_BOOLEAN:
			case K_CALLED:
			case K_CAST:
			case K_CLUSTERING:
			case K_COMPACT:
			case K_CONTAINS:
			case K_COUNT:
			case K_COUNTER:
			case K_CUSTOM:
			case K_DATE:
			case K_DECIMAL:
			case K_DISTINCT:
			case K_DOUBLE:
			case K_DURATION:
			case K_EXISTS:
			case K_FILTERING:
			case K_FINALFUNC:
			case K_FLOAT:
			case K_FROZEN:
			case K_FUNCTION:
			case K_FUNCTIONS:
			case K_GROUP:
			case K_INET:
			case K_INITCOND:
			case K_INPUT:
			case K_INT:
			case K_JSON:
			case K_KEY:
			case K_KEYS:
			case K_KEYSPACES:
			case K_LANGUAGE:
			case K_LIKE:
			case K_LIST:
			case K_LOGIN:
			case K_MAP:
			case K_NOLOGIN:
			case K_NOSUPERUSER:
			case K_OPTIONS:
			case K_PARTITION:
			case K_PASSWORD:
			case K_PER:
			case K_PERMISSION:
			case K_PERMISSIONS:
			case K_RETURNS:
			case K_ROLE:
			case K_ROLES:
			case K_SFUNC:
			case K_SMALLINT:
			case K_STATIC:
			case K_STORAGE:
			case K_STYPE:
			case K_SUPERUSER:
			case K_TEXT:
			case K_TIME:
			case K_TIMESTAMP:
			case K_TIMEUUID:
			case K_TINYINT:
			case K_TRIGGER:
			case K_TTL:
			case K_TUPLE:
			case K_TYPE:
			case K_USER:
			case K_USERS:
			case K_UUID:
			case K_VALUES:
			case K_VARCHAR:
			case K_VARINT:
			case K_WRITETIME:
				{
				alt172=3;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return id;}
				NoViableAltException nvae =
					new NoViableAltException("", 172, 0, input);
				throw nvae;
			}
			switch (alt172) {
				case 1 :
					// Parser.g:1331:7: t= IDENT
					{
					t=(Token)match(input,IDENT,FOLLOW_IDENT_in_fident9094); if (state.failed) return id;
					if ( state.backtracking==0 ) { id = FieldIdentifier.forUnquoted((t!=null?t.getText():null)); }
					}
					break;
				case 2 :
					// Parser.g:1332:7: t= QUOTED_NAME
					{
					t=(Token)match(input,QUOTED_NAME,FOLLOW_QUOTED_NAME_in_fident9119); if (state.failed) return id;
					if ( state.backtracking==0 ) { id = FieldIdentifier.forQuoted((t!=null?t.getText():null)); }
					}
					break;
				case 3 :
					// Parser.g:1333:7: k= unreserved_keyword
					{
					pushFollow(FOLLOW_unreserved_keyword_in_fident9138);
					k=unreserved_keyword();
					state._fsp--;
					if (state.failed) return id;
					if ( state.backtracking==0 ) { id = FieldIdentifier.forUnquoted(k); }
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return id;
	}
	// $ANTLR end "fident"



	// $ANTLR start "noncol_ident"
	// Parser.g:1337:1: noncol_ident returns [ColumnIdentifier id] : (t= IDENT |t= QUOTED_NAME |k= unreserved_keyword );
	public final ColumnIdentifier noncol_ident() throws RecognitionException {
		ColumnIdentifier id = null;


		Token t=null;
		String k =null;

		try {
			// Parser.g:1338:5: (t= IDENT |t= QUOTED_NAME |k= unreserved_keyword )
			int alt173=3;
			switch ( input.LA(1) ) {
			case IDENT:
				{
				alt173=1;
				}
				break;
			case QUOTED_NAME:
				{
				alt173=2;
				}
				break;
			case K_AGGREGATE:
			case K_ALL:
			case K_AS:
			case K_ASCII:
			case K_BIGINT:
			case K_BLOB:
			case K_BOOLEAN:
			case K_CALLED:
			case K_CAST:
			case K_CLUSTERING:
			case K_COMPACT:
			case K_CONTAINS:
			case K_COUNT:
			case K_COUNTER:
			case K_CUSTOM:
			case K_DATE:
			case K_DECIMAL:
			case K_DISTINCT:
			case K_DOUBLE:
			case K_DURATION:
			case K_EXISTS:
			case K_FILTERING:
			case K_FINALFUNC:
			case K_FLOAT:
			case K_FROZEN:
			case K_FUNCTION:
			case K_FUNCTIONS:
			case K_GROUP:
			case K_INET:
			case K_INITCOND:
			case K_INPUT:
			case K_INT:
			case K_JSON:
			case K_KEY:
			case K_KEYS:
			case K_KEYSPACES:
			case K_LANGUAGE:
			case K_LIKE:
			case K_LIST:
			case K_LOGIN:
			case K_MAP:
			case K_NOLOGIN:
			case K_NOSUPERUSER:
			case K_OPTIONS:
			case K_PARTITION:
			case K_PASSWORD:
			case K_PER:
			case K_PERMISSION:
			case K_PERMISSIONS:
			case K_RETURNS:
			case K_ROLE:
			case K_ROLES:
			case K_SFUNC:
			case K_SMALLINT:
			case K_STATIC:
			case K_STORAGE:
			case K_STYPE:
			case K_SUPERUSER:
			case K_TEXT:
			case K_TIME:
			case K_TIMESTAMP:
			case K_TIMEUUID:
			case K_TINYINT:
			case K_TRIGGER:
			case K_TTL:
			case K_TUPLE:
			case K_TYPE:
			case K_USER:
			case K_USERS:
			case K_UUID:
			case K_VALUES:
			case K_VARCHAR:
			case K_VARINT:
			case K_WRITETIME:
				{
				alt173=3;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return id;}
				NoViableAltException nvae =
					new NoViableAltException("", 173, 0, input);
				throw nvae;
			}
			switch (alt173) {
				case 1 :
					// Parser.g:1338:7: t= IDENT
					{
					t=(Token)match(input,IDENT,FOLLOW_IDENT_in_noncol_ident9164); if (state.failed) return id;
					if ( state.backtracking==0 ) { id = new ColumnIdentifier((t!=null?t.getText():null), false); }
					}
					break;
				case 2 :
					// Parser.g:1339:7: t= QUOTED_NAME
					{
					t=(Token)match(input,QUOTED_NAME,FOLLOW_QUOTED_NAME_in_noncol_ident9189); if (state.failed) return id;
					if ( state.backtracking==0 ) { id = new ColumnIdentifier((t!=null?t.getText():null), true); }
					}
					break;
				case 3 :
					// Parser.g:1340:7: k= unreserved_keyword
					{
					pushFollow(FOLLOW_unreserved_keyword_in_noncol_ident9208);
					k=unreserved_keyword();
					state._fsp--;
					if (state.failed) return id;
					if ( state.backtracking==0 ) { id = new ColumnIdentifier(k, false); }
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return id;
	}
	// $ANTLR end "noncol_ident"



	// $ANTLR start "keyspaceName"
	// Parser.g:1344:1: keyspaceName returns [String id] : ksName[name] ;
	public final String keyspaceName() throws RecognitionException {
		String id = null;


		 QualifiedName name = new QualifiedName(); 
		try {
			// Parser.g:1346:5: ( ksName[name] )
			// Parser.g:1346:7: ksName[name]
			{
			pushFollow(FOLLOW_ksName_in_keyspaceName9241);
			ksName(name);
			state._fsp--;
			if (state.failed) return id;
			if ( state.backtracking==0 ) { id = name.getKeyspace(); }
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return id;
	}
	// $ANTLR end "keyspaceName"



	// $ANTLR start "indexName"
	// Parser.g:1349:1: indexName returns [QualifiedName name] : ( ksName[name] '.' )? idxName[name] ;
	public final QualifiedName indexName() throws RecognitionException {
		QualifiedName name = null;


		 name = new QualifiedName(); 
		try {
			// Parser.g:1351:5: ( ( ksName[name] '.' )? idxName[name] )
			// Parser.g:1351:7: ( ksName[name] '.' )? idxName[name]
			{
			// Parser.g:1351:7: ( ksName[name] '.' )?
			int alt174=2;
			alt174 = dfa174.predict(input);
			switch (alt174) {
				case 1 :
					// Parser.g:1351:8: ksName[name] '.'
					{
					pushFollow(FOLLOW_ksName_in_indexName9275);
					ksName(name);
					state._fsp--;
					if (state.failed) return name;
					match(input,197,FOLLOW_197_in_indexName9278); if (state.failed) return name;
					}
					break;

			}

			pushFollow(FOLLOW_idxName_in_indexName9282);
			idxName(name);
			state._fsp--;
			if (state.failed) return name;
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return name;
	}
	// $ANTLR end "indexName"



	// $ANTLR start "columnFamilyName"
	// Parser.g:1354:1: columnFamilyName returns [QualifiedName name] : ( ksName[name] '.' )? cfName[name] ;
	public final QualifiedName columnFamilyName() throws RecognitionException {
		QualifiedName name = null;


		 name = new QualifiedName(); 
		try {
			// Parser.g:1356:5: ( ( ksName[name] '.' )? cfName[name] )
			// Parser.g:1356:7: ( ksName[name] '.' )? cfName[name]
			{
			// Parser.g:1356:7: ( ksName[name] '.' )?
			int alt175=2;
			alt175 = dfa175.predict(input);
			switch (alt175) {
				case 1 :
					// Parser.g:1356:8: ksName[name] '.'
					{
					pushFollow(FOLLOW_ksName_in_columnFamilyName9314);
					ksName(name);
					state._fsp--;
					if (state.failed) return name;
					match(input,197,FOLLOW_197_in_columnFamilyName9317); if (state.failed) return name;
					}
					break;

			}

			pushFollow(FOLLOW_cfName_in_columnFamilyName9321);
			cfName(name);
			state._fsp--;
			if (state.failed) return name;
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return name;
	}
	// $ANTLR end "columnFamilyName"



	// $ANTLR start "userTypeName"
	// Parser.g:1359:1: userTypeName returns [UTName name] : (ks= noncol_ident '.' )? ut= non_type_ident ;
	public final UTName userTypeName() throws RecognitionException {
		UTName name = null;


		ColumnIdentifier ks =null;
		ColumnIdentifier ut =null;

		try {
			// Parser.g:1360:5: ( (ks= noncol_ident '.' )? ut= non_type_ident )
			// Parser.g:1360:7: (ks= noncol_ident '.' )? ut= non_type_ident
			{
			// Parser.g:1360:7: (ks= noncol_ident '.' )?
			int alt176=2;
			switch ( input.LA(1) ) {
				case IDENT:
					{
					int LA176_1 = input.LA(2);
					if ( (LA176_1==197) ) {
						alt176=1;
					}
					}
					break;
				case QUOTED_NAME:
					{
					int LA176_2 = input.LA(2);
					if ( (LA176_2==197) ) {
						alt176=1;
					}
					}
					break;
				case K_AGGREGATE:
				case K_ALL:
				case K_AS:
				case K_CALLED:
				case K_CLUSTERING:
				case K_COMPACT:
				case K_CONTAINS:
				case K_CUSTOM:
				case K_EXISTS:
				case K_FILTERING:
				case K_FINALFUNC:
				case K_FROZEN:
				case K_FUNCTION:
				case K_FUNCTIONS:
				case K_GROUP:
				case K_INITCOND:
				case K_INPUT:
				case K_KEYS:
				case K_KEYSPACES:
				case K_LANGUAGE:
				case K_LIKE:
				case K_LIST:
				case K_LOGIN:
				case K_MAP:
				case K_NOLOGIN:
				case K_NOSUPERUSER:
				case K_OPTIONS:
				case K_PARTITION:
				case K_PASSWORD:
				case K_PER:
				case K_PERMISSION:
				case K_PERMISSIONS:
				case K_RETURNS:
				case K_ROLE:
				case K_ROLES:
				case K_SFUNC:
				case K_STATIC:
				case K_STORAGE:
				case K_STYPE:
				case K_SUPERUSER:
				case K_TRIGGER:
				case K_TUPLE:
				case K_TYPE:
				case K_USER:
				case K_USERS:
				case K_VALUES:
					{
					int LA176_3 = input.LA(2);
					if ( (LA176_3==197) ) {
						alt176=1;
					}
					}
					break;
				case K_ASCII:
				case K_BIGINT:
				case K_BLOB:
				case K_BOOLEAN:
				case K_CAST:
				case K_COUNT:
				case K_COUNTER:
				case K_DATE:
				case K_DECIMAL:
				case K_DISTINCT:
				case K_DOUBLE:
				case K_DURATION:
				case K_FLOAT:
				case K_INET:
				case K_INT:
				case K_JSON:
				case K_SMALLINT:
				case K_TEXT:
				case K_TIME:
				case K_TIMESTAMP:
				case K_TIMEUUID:
				case K_TINYINT:
				case K_TTL:
				case K_UUID:
				case K_VARCHAR:
				case K_VARINT:
				case K_WRITETIME:
					{
					alt176=1;
					}
					break;
				case K_KEY:
					{
					int LA176_5 = input.LA(2);
					if ( (LA176_5==197) ) {
						alt176=1;
					}
					}
					break;
			}
			switch (alt176) {
				case 1 :
					// Parser.g:1360:8: ks= noncol_ident '.'
					{
					pushFollow(FOLLOW_noncol_ident_in_userTypeName9346);
					ks=noncol_ident();
					state._fsp--;
					if (state.failed) return name;
					match(input,197,FOLLOW_197_in_userTypeName9348); if (state.failed) return name;
					}
					break;

			}

			pushFollow(FOLLOW_non_type_ident_in_userTypeName9354);
			ut=non_type_ident();
			state._fsp--;
			if (state.failed) return name;
			if ( state.backtracking==0 ) { name = new UTName(ks, ut); }
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return name;
	}
	// $ANTLR end "userTypeName"



	// $ANTLR start "userOrRoleName"
	// Parser.g:1363:1: userOrRoleName returns [RoleName name] : roleName[role] ;
	public final RoleName userOrRoleName() throws RecognitionException {
		RoleName name = null;


		 RoleName role = new RoleName(); 
		try {
			// Parser.g:1365:5: ( roleName[role] )
			// Parser.g:1365:7: roleName[role]
			{
			pushFollow(FOLLOW_roleName_in_userOrRoleName9386);
			roleName(role);
			state._fsp--;
			if (state.failed) return name;
			if ( state.backtracking==0 ) {name = role;}
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return name;
	}
	// $ANTLR end "userOrRoleName"



	// $ANTLR start "ksName"
	// Parser.g:1368:1: ksName[QualifiedName name] : (t= IDENT |t= QUOTED_NAME |k= unreserved_keyword | QMARK );
	public final void ksName(QualifiedName name) throws RecognitionException {
		Token t=null;
		String k =null;

		try {
			// Parser.g:1369:5: (t= IDENT |t= QUOTED_NAME |k= unreserved_keyword | QMARK )
			int alt177=4;
			switch ( input.LA(1) ) {
			case IDENT:
				{
				alt177=1;
				}
				break;
			case QUOTED_NAME:
				{
				alt177=2;
				}
				break;
			case K_AGGREGATE:
			case K_ALL:
			case K_AS:
			case K_ASCII:
			case K_BIGINT:
			case K_BLOB:
			case K_BOOLEAN:
			case K_CALLED:
			case K_CAST:
			case K_CLUSTERING:
			case K_COMPACT:
			case K_CONTAINS:
			case K_COUNT:
			case K_COUNTER:
			case K_CUSTOM:
			case K_DATE:
			case K_DECIMAL:
			case K_DISTINCT:
			case K_DOUBLE:
			case K_DURATION:
			case K_EXISTS:
			case K_FILTERING:
			case K_FINALFUNC:
			case K_FLOAT:
			case K_FROZEN:
			case K_FUNCTION:
			case K_FUNCTIONS:
			case K_GROUP:
			case K_INET:
			case K_INITCOND:
			case K_INPUT:
			case K_INT:
			case K_JSON:
			case K_KEY:
			case K_KEYS:
			case K_KEYSPACES:
			case K_LANGUAGE:
			case K_LIKE:
			case K_LIST:
			case K_LOGIN:
			case K_MAP:
			case K_NOLOGIN:
			case K_NOSUPERUSER:
			case K_OPTIONS:
			case K_PARTITION:
			case K_PASSWORD:
			case K_PER:
			case K_PERMISSION:
			case K_PERMISSIONS:
			case K_RETURNS:
			case K_ROLE:
			case K_ROLES:
			case K_SFUNC:
			case K_SMALLINT:
			case K_STATIC:
			case K_STORAGE:
			case K_STYPE:
			case K_SUPERUSER:
			case K_TEXT:
			case K_TIME:
			case K_TIMESTAMP:
			case K_TIMEUUID:
			case K_TINYINT:
			case K_TRIGGER:
			case K_TTL:
			case K_TUPLE:
			case K_TYPE:
			case K_USER:
			case K_USERS:
			case K_UUID:
			case K_VALUES:
			case K_VARCHAR:
			case K_VARINT:
			case K_WRITETIME:
				{
				alt177=3;
				}
				break;
			case QMARK:
				{
				alt177=4;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return;}
				NoViableAltException nvae =
					new NoViableAltException("", 177, 0, input);
				throw nvae;
			}
			switch (alt177) {
				case 1 :
					// Parser.g:1369:7: t= IDENT
					{
					t=(Token)match(input,IDENT,FOLLOW_IDENT_in_ksName9409); if (state.failed) return;
					if ( state.backtracking==0 ) { name.setKeyspace((t!=null?t.getText():null), false);}
					}
					break;
				case 2 :
					// Parser.g:1370:7: t= QUOTED_NAME
					{
					t=(Token)match(input,QUOTED_NAME,FOLLOW_QUOTED_NAME_in_ksName9434); if (state.failed) return;
					if ( state.backtracking==0 ) { name.setKeyspace((t!=null?t.getText():null), true);}
					}
					break;
				case 3 :
					// Parser.g:1371:7: k= unreserved_keyword
					{
					pushFollow(FOLLOW_unreserved_keyword_in_ksName9453);
					k=unreserved_keyword();
					state._fsp--;
					if (state.failed) return;
					if ( state.backtracking==0 ) { name.setKeyspace(k, false);}
					}
					break;
				case 4 :
					// Parser.g:1372:7: QMARK
					{
					match(input,QMARK,FOLLOW_QMARK_in_ksName9463); if (state.failed) return;
					if ( state.backtracking==0 ) {addRecognitionError("Bind variables cannot be used for keyspace names");}
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "ksName"



	// $ANTLR start "cfName"
	// Parser.g:1375:1: cfName[QualifiedName name] : (t= IDENT |t= QUOTED_NAME |k= unreserved_keyword | QMARK );
	public final void cfName(QualifiedName name) throws RecognitionException {
		Token t=null;
		String k =null;

		try {
			// Parser.g:1376:5: (t= IDENT |t= QUOTED_NAME |k= unreserved_keyword | QMARK )
			int alt178=4;
			switch ( input.LA(1) ) {
			case IDENT:
				{
				alt178=1;
				}
				break;
			case QUOTED_NAME:
				{
				alt178=2;
				}
				break;
			case K_AGGREGATE:
			case K_ALL:
			case K_AS:
			case K_ASCII:
			case K_BIGINT:
			case K_BLOB:
			case K_BOOLEAN:
			case K_CALLED:
			case K_CAST:
			case K_CLUSTERING:
			case K_COMPACT:
			case K_CONTAINS:
			case K_COUNT:
			case K_COUNTER:
			case K_CUSTOM:
			case K_DATE:
			case K_DECIMAL:
			case K_DISTINCT:
			case K_DOUBLE:
			case K_DURATION:
			case K_EXISTS:
			case K_FILTERING:
			case K_FINALFUNC:
			case K_FLOAT:
			case K_FROZEN:
			case K_FUNCTION:
			case K_FUNCTIONS:
			case K_GROUP:
			case K_INET:
			case K_INITCOND:
			case K_INPUT:
			case K_INT:
			case K_JSON:
			case K_KEY:
			case K_KEYS:
			case K_KEYSPACES:
			case K_LANGUAGE:
			case K_LIKE:
			case K_LIST:
			case K_LOGIN:
			case K_MAP:
			case K_NOLOGIN:
			case K_NOSUPERUSER:
			case K_OPTIONS:
			case K_PARTITION:
			case K_PASSWORD:
			case K_PER:
			case K_PERMISSION:
			case K_PERMISSIONS:
			case K_RETURNS:
			case K_ROLE:
			case K_ROLES:
			case K_SFUNC:
			case K_SMALLINT:
			case K_STATIC:
			case K_STORAGE:
			case K_STYPE:
			case K_SUPERUSER:
			case K_TEXT:
			case K_TIME:
			case K_TIMESTAMP:
			case K_TIMEUUID:
			case K_TINYINT:
			case K_TRIGGER:
			case K_TTL:
			case K_TUPLE:
			case K_TYPE:
			case K_USER:
			case K_USERS:
			case K_UUID:
			case K_VALUES:
			case K_VARCHAR:
			case K_VARINT:
			case K_WRITETIME:
				{
				alt178=3;
				}
				break;
			case QMARK:
				{
				alt178=4;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return;}
				NoViableAltException nvae =
					new NoViableAltException("", 178, 0, input);
				throw nvae;
			}
			switch (alt178) {
				case 1 :
					// Parser.g:1376:7: t= IDENT
					{
					t=(Token)match(input,IDENT,FOLLOW_IDENT_in_cfName9485); if (state.failed) return;
					if ( state.backtracking==0 ) { name.setName((t!=null?t.getText():null), false); }
					}
					break;
				case 2 :
					// Parser.g:1377:7: t= QUOTED_NAME
					{
					t=(Token)match(input,QUOTED_NAME,FOLLOW_QUOTED_NAME_in_cfName9510); if (state.failed) return;
					if ( state.backtracking==0 ) { name.setName((t!=null?t.getText():null), true); }
					}
					break;
				case 3 :
					// Parser.g:1378:7: k= unreserved_keyword
					{
					pushFollow(FOLLOW_unreserved_keyword_in_cfName9529);
					k=unreserved_keyword();
					state._fsp--;
					if (state.failed) return;
					if ( state.backtracking==0 ) { name.setName(k, false); }
					}
					break;
				case 4 :
					// Parser.g:1379:7: QMARK
					{
					match(input,QMARK,FOLLOW_QMARK_in_cfName9539); if (state.failed) return;
					if ( state.backtracking==0 ) {addRecognitionError("Bind variables cannot be used for table names");}
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "cfName"



	// $ANTLR start "idxName"
	// Parser.g:1382:1: idxName[QualifiedName name] : (t= IDENT |t= QUOTED_NAME |k= unreserved_keyword | QMARK );
	public final void idxName(QualifiedName name) throws RecognitionException {
		Token t=null;
		String k =null;

		try {
			// Parser.g:1383:5: (t= IDENT |t= QUOTED_NAME |k= unreserved_keyword | QMARK )
			int alt179=4;
			switch ( input.LA(1) ) {
			case IDENT:
				{
				alt179=1;
				}
				break;
			case QUOTED_NAME:
				{
				alt179=2;
				}
				break;
			case K_AGGREGATE:
			case K_ALL:
			case K_AS:
			case K_ASCII:
			case K_BIGINT:
			case K_BLOB:
			case K_BOOLEAN:
			case K_CALLED:
			case K_CAST:
			case K_CLUSTERING:
			case K_COMPACT:
			case K_CONTAINS:
			case K_COUNT:
			case K_COUNTER:
			case K_CUSTOM:
			case K_DATE:
			case K_DECIMAL:
			case K_DISTINCT:
			case K_DOUBLE:
			case K_DURATION:
			case K_EXISTS:
			case K_FILTERING:
			case K_FINALFUNC:
			case K_FLOAT:
			case K_FROZEN:
			case K_FUNCTION:
			case K_FUNCTIONS:
			case K_GROUP:
			case K_INET:
			case K_INITCOND:
			case K_INPUT:
			case K_INT:
			case K_JSON:
			case K_KEY:
			case K_KEYS:
			case K_KEYSPACES:
			case K_LANGUAGE:
			case K_LIKE:
			case K_LIST:
			case K_LOGIN:
			case K_MAP:
			case K_NOLOGIN:
			case K_NOSUPERUSER:
			case K_OPTIONS:
			case K_PARTITION:
			case K_PASSWORD:
			case K_PER:
			case K_PERMISSION:
			case K_PERMISSIONS:
			case K_RETURNS:
			case K_ROLE:
			case K_ROLES:
			case K_SFUNC:
			case K_SMALLINT:
			case K_STATIC:
			case K_STORAGE:
			case K_STYPE:
			case K_SUPERUSER:
			case K_TEXT:
			case K_TIME:
			case K_TIMESTAMP:
			case K_TIMEUUID:
			case K_TINYINT:
			case K_TRIGGER:
			case K_TTL:
			case K_TUPLE:
			case K_TYPE:
			case K_USER:
			case K_USERS:
			case K_UUID:
			case K_VALUES:
			case K_VARCHAR:
			case K_VARINT:
			case K_WRITETIME:
				{
				alt179=3;
				}
				break;
			case QMARK:
				{
				alt179=4;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return;}
				NoViableAltException nvae =
					new NoViableAltException("", 179, 0, input);
				throw nvae;
			}
			switch (alt179) {
				case 1 :
					// Parser.g:1383:7: t= IDENT
					{
					t=(Token)match(input,IDENT,FOLLOW_IDENT_in_idxName9561); if (state.failed) return;
					if ( state.backtracking==0 ) { name.setName((t!=null?t.getText():null), false); }
					}
					break;
				case 2 :
					// Parser.g:1384:7: t= QUOTED_NAME
					{
					t=(Token)match(input,QUOTED_NAME,FOLLOW_QUOTED_NAME_in_idxName9586); if (state.failed) return;
					if ( state.backtracking==0 ) { name.setName((t!=null?t.getText():null), true);}
					}
					break;
				case 3 :
					// Parser.g:1385:7: k= unreserved_keyword
					{
					pushFollow(FOLLOW_unreserved_keyword_in_idxName9605);
					k=unreserved_keyword();
					state._fsp--;
					if (state.failed) return;
					if ( state.backtracking==0 ) { name.setName(k, false); }
					}
					break;
				case 4 :
					// Parser.g:1386:7: QMARK
					{
					match(input,QMARK,FOLLOW_QMARK_in_idxName9615); if (state.failed) return;
					if ( state.backtracking==0 ) {addRecognitionError("Bind variables cannot be used for index names");}
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "idxName"



	// $ANTLR start "roleName"
	// Parser.g:1389:1: roleName[RoleName name] : (t= IDENT |s= STRING_LITERAL |t= QUOTED_NAME |k= unreserved_keyword | QMARK );
	public final void roleName(RoleName name) throws RecognitionException {
		Token t=null;
		Token s=null;
		String k =null;

		try {
			// Parser.g:1390:5: (t= IDENT |s= STRING_LITERAL |t= QUOTED_NAME |k= unreserved_keyword | QMARK )
			int alt180=5;
			switch ( input.LA(1) ) {
			case IDENT:
				{
				alt180=1;
				}
				break;
			case STRING_LITERAL:
				{
				alt180=2;
				}
				break;
			case QUOTED_NAME:
				{
				alt180=3;
				}
				break;
			case K_AGGREGATE:
			case K_ALL:
			case K_AS:
			case K_ASCII:
			case K_BIGINT:
			case K_BLOB:
			case K_BOOLEAN:
			case K_CALLED:
			case K_CAST:
			case K_CLUSTERING:
			case K_COMPACT:
			case K_CONTAINS:
			case K_COUNT:
			case K_COUNTER:
			case K_CUSTOM:
			case K_DATE:
			case K_DECIMAL:
			case K_DISTINCT:
			case K_DOUBLE:
			case K_DURATION:
			case K_EXISTS:
			case K_FILTERING:
			case K_FINALFUNC:
			case K_FLOAT:
			case K_FROZEN:
			case K_FUNCTION:
			case K_FUNCTIONS:
			case K_GROUP:
			case K_INET:
			case K_INITCOND:
			case K_INPUT:
			case K_INT:
			case K_JSON:
			case K_KEY:
			case K_KEYS:
			case K_KEYSPACES:
			case K_LANGUAGE:
			case K_LIKE:
			case K_LIST:
			case K_LOGIN:
			case K_MAP:
			case K_NOLOGIN:
			case K_NOSUPERUSER:
			case K_OPTIONS:
			case K_PARTITION:
			case K_PASSWORD:
			case K_PER:
			case K_PERMISSION:
			case K_PERMISSIONS:
			case K_RETURNS:
			case K_ROLE:
			case K_ROLES:
			case K_SFUNC:
			case K_SMALLINT:
			case K_STATIC:
			case K_STORAGE:
			case K_STYPE:
			case K_SUPERUSER:
			case K_TEXT:
			case K_TIME:
			case K_TIMESTAMP:
			case K_TIMEUUID:
			case K_TINYINT:
			case K_TRIGGER:
			case K_TTL:
			case K_TUPLE:
			case K_TYPE:
			case K_USER:
			case K_USERS:
			case K_UUID:
			case K_VALUES:
			case K_VARCHAR:
			case K_VARINT:
			case K_WRITETIME:
				{
				alt180=4;
				}
				break;
			case QMARK:
				{
				alt180=5;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return;}
				NoViableAltException nvae =
					new NoViableAltException("", 180, 0, input);
				throw nvae;
			}
			switch (alt180) {
				case 1 :
					// Parser.g:1390:7: t= IDENT
					{
					t=(Token)match(input,IDENT,FOLLOW_IDENT_in_roleName9637); if (state.failed) return;
					if ( state.backtracking==0 ) { name.setName((t!=null?t.getText():null), false); }
					}
					break;
				case 2 :
					// Parser.g:1391:7: s= STRING_LITERAL
					{
					s=(Token)match(input,STRING_LITERAL,FOLLOW_STRING_LITERAL_in_roleName9662); if (state.failed) return;
					if ( state.backtracking==0 ) { name.setName((s!=null?s.getText():null), true); }
					}
					break;
				case 3 :
					// Parser.g:1392:7: t= QUOTED_NAME
					{
					t=(Token)match(input,QUOTED_NAME,FOLLOW_QUOTED_NAME_in_roleName9678); if (state.failed) return;
					if ( state.backtracking==0 ) { name.setName((t!=null?t.getText():null), true); }
					}
					break;
				case 4 :
					// Parser.g:1393:7: k= unreserved_keyword
					{
					pushFollow(FOLLOW_unreserved_keyword_in_roleName9697);
					k=unreserved_keyword();
					state._fsp--;
					if (state.failed) return;
					if ( state.backtracking==0 ) { name.setName(k, false); }
					}
					break;
				case 5 :
					// Parser.g:1394:7: QMARK
					{
					match(input,QMARK,FOLLOW_QMARK_in_roleName9707); if (state.failed) return;
					if ( state.backtracking==0 ) {addRecognitionError("Bind variables cannot be used for role names");}
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "roleName"



	// $ANTLR start "constant"
	// Parser.g:1397:1: constant returns [Constants.Literal constant] : (t= STRING_LITERAL |t= INTEGER |t= FLOAT |t= BOOLEAN |t= DURATION |t= UUID |t= HEXNUMBER | ( ( K_POSITIVE_NAN | K_NEGATIVE_NAN ) | K_POSITIVE_INFINITY | K_NEGATIVE_INFINITY ) );
	public final Constants.Literal constant() throws RecognitionException {
		Constants.Literal constant = null;


		Token t=null;

		try {
			// Parser.g:1398:5: (t= STRING_LITERAL |t= INTEGER |t= FLOAT |t= BOOLEAN |t= DURATION |t= UUID |t= HEXNUMBER | ( ( K_POSITIVE_NAN | K_NEGATIVE_NAN ) | K_POSITIVE_INFINITY | K_NEGATIVE_INFINITY ) )
			int alt182=8;
			switch ( input.LA(1) ) {
			case STRING_LITERAL:
				{
				alt182=1;
				}
				break;
			case INTEGER:
				{
				alt182=2;
				}
				break;
			case FLOAT:
				{
				alt182=3;
				}
				break;
			case BOOLEAN:
				{
				alt182=4;
				}
				break;
			case DURATION:
				{
				alt182=5;
				}
				break;
			case UUID:
				{
				alt182=6;
				}
				break;
			case HEXNUMBER:
				{
				alt182=7;
				}
				break;
			case K_NEGATIVE_INFINITY:
			case K_NEGATIVE_NAN:
			case K_POSITIVE_INFINITY:
			case K_POSITIVE_NAN:
				{
				alt182=8;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return constant;}
				NoViableAltException nvae =
					new NoViableAltException("", 182, 0, input);
				throw nvae;
			}
			switch (alt182) {
				case 1 :
					// Parser.g:1398:7: t= STRING_LITERAL
					{
					t=(Token)match(input,STRING_LITERAL,FOLLOW_STRING_LITERAL_in_constant9732); if (state.failed) return constant;
					if ( state.backtracking==0 ) { constant = Constants.Literal.string((t!=null?t.getText():null)); }
					}
					break;
				case 2 :
					// Parser.g:1399:7: t= INTEGER
					{
					t=(Token)match(input,INTEGER,FOLLOW_INTEGER_in_constant9744); if (state.failed) return constant;
					if ( state.backtracking==0 ) { constant = Constants.Literal.integer((t!=null?t.getText():null)); }
					}
					break;
				case 3 :
					// Parser.g:1400:7: t= FLOAT
					{
					t=(Token)match(input,FLOAT,FOLLOW_FLOAT_in_constant9763); if (state.failed) return constant;
					if ( state.backtracking==0 ) { constant = Constants.Literal.floatingPoint((t!=null?t.getText():null)); }
					}
					break;
				case 4 :
					// Parser.g:1401:7: t= BOOLEAN
					{
					t=(Token)match(input,BOOLEAN,FOLLOW_BOOLEAN_in_constant9784); if (state.failed) return constant;
					if ( state.backtracking==0 ) { constant = Constants.Literal.bool((t!=null?t.getText():null)); }
					}
					break;
				case 5 :
					// Parser.g:1402:7: t= DURATION
					{
					t=(Token)match(input,DURATION,FOLLOW_DURATION_in_constant9803); if (state.failed) return constant;
					if ( state.backtracking==0 ) { constant = Constants.Literal.duration((t!=null?t.getText():null));}
					}
					break;
				case 6 :
					// Parser.g:1403:7: t= UUID
					{
					t=(Token)match(input,UUID,FOLLOW_UUID_in_constant9821); if (state.failed) return constant;
					if ( state.backtracking==0 ) { constant = Constants.Literal.uuid((t!=null?t.getText():null)); }
					}
					break;
				case 7 :
					// Parser.g:1404:7: t= HEXNUMBER
					{
					t=(Token)match(input,HEXNUMBER,FOLLOW_HEXNUMBER_in_constant9843); if (state.failed) return constant;
					if ( state.backtracking==0 ) { constant = Constants.Literal.hex((t!=null?t.getText():null)); }
					}
					break;
				case 8 :
					// Parser.g:1405:7: ( ( K_POSITIVE_NAN | K_NEGATIVE_NAN ) | K_POSITIVE_INFINITY | K_NEGATIVE_INFINITY )
					{
					// Parser.g:1405:7: ( ( K_POSITIVE_NAN | K_NEGATIVE_NAN ) | K_POSITIVE_INFINITY | K_NEGATIVE_INFINITY )
					int alt181=3;
					switch ( input.LA(1) ) {
					case K_NEGATIVE_NAN:
					case K_POSITIVE_NAN:
						{
						alt181=1;
						}
						break;
					case K_POSITIVE_INFINITY:
						{
						alt181=2;
						}
						break;
					case K_NEGATIVE_INFINITY:
						{
						alt181=3;
						}
						break;
					default:
						if (state.backtracking>0) {state.failed=true; return constant;}
						NoViableAltException nvae =
							new NoViableAltException("", 181, 0, input);
						throw nvae;
					}
					switch (alt181) {
						case 1 :
							// Parser.g:1405:8: ( K_POSITIVE_NAN | K_NEGATIVE_NAN )
							{
							if ( input.LA(1)==K_NEGATIVE_NAN||input.LA(1)==K_POSITIVE_NAN ) {
								input.consume();
								state.errorRecovery=false;
								state.failed=false;
							}
							else {
								if (state.backtracking>0) {state.failed=true; return constant;}
								MismatchedSetException mse = new MismatchedSetException(null,input);
								throw mse;
							}
							if ( state.backtracking==0 ) { constant = Constants.Literal.floatingPoint("NaN"); }
							}
							break;
						case 2 :
							// Parser.g:1406:11: K_POSITIVE_INFINITY
							{
							match(input,K_POSITIVE_INFINITY,FOLLOW_K_POSITIVE_INFINITY_in_constant9879); if (state.failed) return constant;
							if ( state.backtracking==0 ) { constant = Constants.Literal.floatingPoint("Infinity"); }
							}
							break;
						case 3 :
							// Parser.g:1407:11: K_NEGATIVE_INFINITY
							{
							match(input,K_NEGATIVE_INFINITY,FOLLOW_K_NEGATIVE_INFINITY_in_constant9894); if (state.failed) return constant;
							if ( state.backtracking==0 ) { constant = Constants.Literal.floatingPoint("-Infinity"); }
							}
							break;

					}

					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return constant;
	}
	// $ANTLR end "constant"



	// $ANTLR start "fullMapLiteral"
	// Parser.g:1410:1: fullMapLiteral returns [Maps.Literal map] : '{' (k1= term ':' v1= term ( ',' kn= term ':' vn= term )* )? '}' ;
	public final Maps.Literal fullMapLiteral() throws RecognitionException {
		Maps.Literal map = null;


		Term.Raw k1 =null;
		Term.Raw v1 =null;
		Term.Raw kn =null;
		Term.Raw vn =null;

		 List<Pair<Term.Raw, Term.Raw>> m = new ArrayList<Pair<Term.Raw, Term.Raw>>();
		try {
			// Parser.g:1413:5: ( '{' (k1= term ':' v1= term ( ',' kn= term ':' vn= term )* )? '}' )
			// Parser.g:1413:7: '{' (k1= term ':' v1= term ( ',' kn= term ':' vn= term )* )? '}'
			{
			match(input,210,FOLLOW_210_in_fullMapLiteral9935); if (state.failed) return map;
			// Parser.g:1413:11: (k1= term ':' v1= term ( ',' kn= term ':' vn= term )* )?
			int alt184=2;
			int LA184_0 = input.LA(1);
			if ( (LA184_0==BOOLEAN||LA184_0==DURATION||LA184_0==FLOAT||LA184_0==HEXNUMBER||(LA184_0 >= IDENT && LA184_0 <= INTEGER)||(LA184_0 >= K_AGGREGATE && LA184_0 <= K_ALL)||LA184_0==K_AS||LA184_0==K_ASCII||(LA184_0 >= K_BIGINT && LA184_0 <= K_BOOLEAN)||(LA184_0 >= K_CALLED && LA184_0 <= K_CLUSTERING)||(LA184_0 >= K_COMPACT && LA184_0 <= K_COUNTER)||LA184_0==K_CUSTOM||(LA184_0 >= K_DATE && LA184_0 <= K_DECIMAL)||(LA184_0 >= K_DISTINCT && LA184_0 <= K_DOUBLE)||LA184_0==K_DURATION||(LA184_0 >= K_EXISTS && LA184_0 <= K_FLOAT)||LA184_0==K_FROZEN||(LA184_0 >= K_FUNCTION && LA184_0 <= K_FUNCTIONS)||LA184_0==K_GROUP||(LA184_0 >= K_INET && LA184_0 <= K_INPUT)||LA184_0==K_INT||(LA184_0 >= K_JSON && LA184_0 <= K_KEYS)||(LA184_0 >= K_KEYSPACES && LA184_0 <= K_LIKE)||(LA184_0 >= K_LIST && LA184_0 <= K_MAP)||(LA184_0 >= K_NEGATIVE_INFINITY && LA184_0 <= K_NOLOGIN)||LA184_0==K_NOSUPERUSER||LA184_0==K_NULL||LA184_0==K_OPTIONS||(LA184_0 >= K_PARTITION && LA184_0 <= K_POSITIVE_NAN)||LA184_0==K_RETURNS||(LA184_0 >= K_ROLE && LA184_0 <= K_ROLES)||(LA184_0 >= K_SFUNC && LA184_0 <= K_TINYINT)||(LA184_0 >= K_TOKEN && LA184_0 <= K_TRIGGER)||(LA184_0 >= K_TTL && LA184_0 <= K_TYPE)||(LA184_0 >= K_USER && LA184_0 <= K_USERS)||(LA184_0 >= K_UUID && LA184_0 <= K_VARINT)||LA184_0==K_WRITETIME||(LA184_0 >= QMARK && LA184_0 <= QUOTED_NAME)||LA184_0==STRING_LITERAL||LA184_0==UUID||LA184_0==190||LA184_0==195||LA184_0==199||LA184_0==206||LA184_0==210) ) {
				alt184=1;
			}
			switch (alt184) {
				case 1 :
					// Parser.g:1413:13: k1= term ':' v1= term ( ',' kn= term ':' vn= term )*
					{
					pushFollow(FOLLOW_term_in_fullMapLiteral9941);
					k1=term();
					state._fsp--;
					if (state.failed) return map;
					match(input,199,FOLLOW_199_in_fullMapLiteral9943); if (state.failed) return map;
					pushFollow(FOLLOW_term_in_fullMapLiteral9947);
					v1=term();
					state._fsp--;
					if (state.failed) return map;
					if ( state.backtracking==0 ) { m.add(Pair.create(k1, v1)); }
					// Parser.g:1413:65: ( ',' kn= term ':' vn= term )*
					loop183:
					while (true) {
						int alt183=2;
						int LA183_0 = input.LA(1);
						if ( (LA183_0==194) ) {
							alt183=1;
						}

						switch (alt183) {
						case 1 :
							// Parser.g:1413:67: ',' kn= term ':' vn= term
							{
							match(input,194,FOLLOW_194_in_fullMapLiteral9953); if (state.failed) return map;
							pushFollow(FOLLOW_term_in_fullMapLiteral9957);
							kn=term();
							state._fsp--;
							if (state.failed) return map;
							match(input,199,FOLLOW_199_in_fullMapLiteral9959); if (state.failed) return map;
							pushFollow(FOLLOW_term_in_fullMapLiteral9963);
							vn=term();
							state._fsp--;
							if (state.failed) return map;
							if ( state.backtracking==0 ) { m.add(Pair.create(kn, vn)); }
							}
							break;

						default :
							break loop183;
						}
					}

					}
					break;

			}

			match(input,211,FOLLOW_211_in_fullMapLiteral9979); if (state.failed) return map;
			}

			if ( state.backtracking==0 ) { map = new Maps.Literal(m); }
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return map;
	}
	// $ANTLR end "fullMapLiteral"



	// $ANTLR start "setOrMapLiteral"
	// Parser.g:1417:1: setOrMapLiteral[Term.Raw t] returns [Term.Raw value] : (m= mapLiteral[t] |s= setLiteral[t] );
	public final Term.Raw setOrMapLiteral(Term.Raw t) throws RecognitionException {
		Term.Raw value = null;


		Term.Raw m =null;
		Term.Raw s =null;

		try {
			// Parser.g:1418:5: (m= mapLiteral[t] |s= setLiteral[t] )
			int alt185=2;
			int LA185_0 = input.LA(1);
			if ( (LA185_0==199) ) {
				alt185=1;
			}
			else if ( (LA185_0==194||LA185_0==211) ) {
				alt185=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return value;}
				NoViableAltException nvae =
					new NoViableAltException("", 185, 0, input);
				throw nvae;
			}

			switch (alt185) {
				case 1 :
					// Parser.g:1418:7: m= mapLiteral[t]
					{
					pushFollow(FOLLOW_mapLiteral_in_setOrMapLiteral10003);
					m=mapLiteral(t);
					state._fsp--;
					if (state.failed) return value;
					if ( state.backtracking==0 ) { value =m; }
					}
					break;
				case 2 :
					// Parser.g:1419:7: s= setLiteral[t]
					{
					pushFollow(FOLLOW_setLiteral_in_setOrMapLiteral10016);
					s=setLiteral(t);
					state._fsp--;
					if (state.failed) return value;
					if ( state.backtracking==0 ) { value =s; }
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return value;
	}
	// $ANTLR end "setOrMapLiteral"



	// $ANTLR start "setLiteral"
	// Parser.g:1422:1: setLiteral[Term.Raw t] returns [Term.Raw value] : ( ',' tn= term )* ;
	public final Term.Raw setLiteral(Term.Raw t) throws RecognitionException {
		Term.Raw value = null;


		Term.Raw tn =null;

		 List<Term.Raw> s = new ArrayList<Term.Raw>(); s.add(t); 
		try {
			// Parser.g:1425:5: ( ( ',' tn= term )* )
			// Parser.g:1425:7: ( ',' tn= term )*
			{
			// Parser.g:1425:7: ( ',' tn= term )*
			loop186:
			while (true) {
				int alt186=2;
				int LA186_0 = input.LA(1);
				if ( (LA186_0==194) ) {
					alt186=1;
				}

				switch (alt186) {
				case 1 :
					// Parser.g:1425:9: ',' tn= term
					{
					match(input,194,FOLLOW_194_in_setLiteral10061); if (state.failed) return value;
					pushFollow(FOLLOW_term_in_setLiteral10065);
					tn=term();
					state._fsp--;
					if (state.failed) return value;
					if ( state.backtracking==0 ) { s.add(tn); }
					}
					break;

				default :
					break loop186;
				}
			}

			}

			if ( state.backtracking==0 ) { value = new Sets.Literal(s); }
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return value;
	}
	// $ANTLR end "setLiteral"



	// $ANTLR start "mapLiteral"
	// Parser.g:1428:1: mapLiteral[Term.Raw k] returns [Term.Raw value] : ':' v= term ( ',' kn= term ':' vn= term )* ;
	public final Term.Raw mapLiteral(Term.Raw k) throws RecognitionException {
		Term.Raw value = null;


		Term.Raw v =null;
		Term.Raw kn =null;
		Term.Raw vn =null;

		 List<Pair<Term.Raw, Term.Raw>> m = new ArrayList<Pair<Term.Raw, Term.Raw>>(); 
		try {
			// Parser.g:1431:5: ( ':' v= term ( ',' kn= term ':' vn= term )* )
			// Parser.g:1431:7: ':' v= term ( ',' kn= term ':' vn= term )*
			{
			match(input,199,FOLLOW_199_in_mapLiteral10110); if (state.failed) return value;
			pushFollow(FOLLOW_term_in_mapLiteral10114);
			v=term();
			state._fsp--;
			if (state.failed) return value;
			if ( state.backtracking==0 ) {  m.add(Pair.create(k, v)); }
			// Parser.g:1431:49: ( ',' kn= term ':' vn= term )*
			loop187:
			while (true) {
				int alt187=2;
				int LA187_0 = input.LA(1);
				if ( (LA187_0==194) ) {
					alt187=1;
				}

				switch (alt187) {
				case 1 :
					// Parser.g:1431:51: ',' kn= term ':' vn= term
					{
					match(input,194,FOLLOW_194_in_mapLiteral10120); if (state.failed) return value;
					pushFollow(FOLLOW_term_in_mapLiteral10124);
					kn=term();
					state._fsp--;
					if (state.failed) return value;
					match(input,199,FOLLOW_199_in_mapLiteral10126); if (state.failed) return value;
					pushFollow(FOLLOW_term_in_mapLiteral10130);
					vn=term();
					state._fsp--;
					if (state.failed) return value;
					if ( state.backtracking==0 ) { m.add(Pair.create(kn, vn)); }
					}
					break;

				default :
					break loop187;
				}
			}

			}

			if ( state.backtracking==0 ) { value = new Maps.Literal(m); }
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return value;
	}
	// $ANTLR end "mapLiteral"



	// $ANTLR start "collectionLiteral"
	// Parser.g:1434:1: collectionLiteral returns [Term.Raw value] : (l= listLiteral | '{' t= term v= setOrMapLiteral[t] '}' | '{' '}' );
	public final Term.Raw collectionLiteral() throws RecognitionException {
		Term.Raw value = null;


		Term.Raw l =null;
		Term.Raw t =null;
		Term.Raw v =null;

		try {
			// Parser.g:1435:5: (l= listLiteral | '{' t= term v= setOrMapLiteral[t] '}' | '{' '}' )
			int alt188=3;
			int LA188_0 = input.LA(1);
			if ( (LA188_0==206) ) {
				alt188=1;
			}
			else if ( (LA188_0==210) ) {
				int LA188_2 = input.LA(2);
				if ( (LA188_2==211) ) {
					alt188=3;
				}
				else if ( (LA188_2==BOOLEAN||LA188_2==DURATION||LA188_2==FLOAT||LA188_2==HEXNUMBER||(LA188_2 >= IDENT && LA188_2 <= INTEGER)||(LA188_2 >= K_AGGREGATE && LA188_2 <= K_ALL)||LA188_2==K_AS||LA188_2==K_ASCII||(LA188_2 >= K_BIGINT && LA188_2 <= K_BOOLEAN)||(LA188_2 >= K_CALLED && LA188_2 <= K_CLUSTERING)||(LA188_2 >= K_COMPACT && LA188_2 <= K_COUNTER)||LA188_2==K_CUSTOM||(LA188_2 >= K_DATE && LA188_2 <= K_DECIMAL)||(LA188_2 >= K_DISTINCT && LA188_2 <= K_DOUBLE)||LA188_2==K_DURATION||(LA188_2 >= K_EXISTS && LA188_2 <= K_FLOAT)||LA188_2==K_FROZEN||(LA188_2 >= K_FUNCTION && LA188_2 <= K_FUNCTIONS)||LA188_2==K_GROUP||(LA188_2 >= K_INET && LA188_2 <= K_INPUT)||LA188_2==K_INT||(LA188_2 >= K_JSON && LA188_2 <= K_KEYS)||(LA188_2 >= K_KEYSPACES && LA188_2 <= K_LIKE)||(LA188_2 >= K_LIST && LA188_2 <= K_MAP)||(LA188_2 >= K_NEGATIVE_INFINITY && LA188_2 <= K_NOLOGIN)||LA188_2==K_NOSUPERUSER||LA188_2==K_NULL||LA188_2==K_OPTIONS||(LA188_2 >= K_PARTITION && LA188_2 <= K_POSITIVE_NAN)||LA188_2==K_RETURNS||(LA188_2 >= K_ROLE && LA188_2 <= K_ROLES)||(LA188_2 >= K_SFUNC && LA188_2 <= K_TINYINT)||(LA188_2 >= K_TOKEN && LA188_2 <= K_TRIGGER)||(LA188_2 >= K_TTL && LA188_2 <= K_TYPE)||(LA188_2 >= K_USER && LA188_2 <= K_USERS)||(LA188_2 >= K_UUID && LA188_2 <= K_VARINT)||LA188_2==K_WRITETIME||(LA188_2 >= QMARK && LA188_2 <= QUOTED_NAME)||LA188_2==STRING_LITERAL||LA188_2==UUID||LA188_2==190||LA188_2==195||LA188_2==199||LA188_2==206||LA188_2==210) ) {
					alt188=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return value;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 188, 2, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

			}

			else {
				if (state.backtracking>0) {state.failed=true; return value;}
				NoViableAltException nvae =
					new NoViableAltException("", 188, 0, input);
				throw nvae;
			}

			switch (alt188) {
				case 1 :
					// Parser.g:1435:7: l= listLiteral
					{
					pushFollow(FOLLOW_listLiteral_in_collectionLiteral10158);
					l=listLiteral();
					state._fsp--;
					if (state.failed) return value;
					if ( state.backtracking==0 ) { value = l; }
					}
					break;
				case 2 :
					// Parser.g:1436:7: '{' t= term v= setOrMapLiteral[t] '}'
					{
					match(input,210,FOLLOW_210_in_collectionLiteral10168); if (state.failed) return value;
					pushFollow(FOLLOW_term_in_collectionLiteral10172);
					t=term();
					state._fsp--;
					if (state.failed) return value;
					pushFollow(FOLLOW_setOrMapLiteral_in_collectionLiteral10176);
					v=setOrMapLiteral(t);
					state._fsp--;
					if (state.failed) return value;
					if ( state.backtracking==0 ) { value = v; }
					match(input,211,FOLLOW_211_in_collectionLiteral10181); if (state.failed) return value;
					}
					break;
				case 3 :
					// Parser.g:1439:7: '{' '}'
					{
					match(input,210,FOLLOW_210_in_collectionLiteral10199); if (state.failed) return value;
					match(input,211,FOLLOW_211_in_collectionLiteral10201); if (state.failed) return value;
					if ( state.backtracking==0 ) { value = new Sets.Literal(Collections.<Term.Raw>emptyList()); }
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return value;
	}
	// $ANTLR end "collectionLiteral"



	// $ANTLR start "listLiteral"
	// Parser.g:1442:1: listLiteral returns [Term.Raw value] : '[' (t1= term ( ',' tn= term )* )? ']' ;
	public final Term.Raw listLiteral() throws RecognitionException {
		Term.Raw value = null;


		Term.Raw t1 =null;
		Term.Raw tn =null;

		List<Term.Raw> l = new ArrayList<Term.Raw>();
		try {
			// Parser.g:1445:5: ( '[' (t1= term ( ',' tn= term )* )? ']' )
			// Parser.g:1445:7: '[' (t1= term ( ',' tn= term )* )? ']'
			{
			match(input,206,FOLLOW_206_in_listLiteral10242); if (state.failed) return value;
			// Parser.g:1445:11: (t1= term ( ',' tn= term )* )?
			int alt190=2;
			int LA190_0 = input.LA(1);
			if ( (LA190_0==BOOLEAN||LA190_0==DURATION||LA190_0==FLOAT||LA190_0==HEXNUMBER||(LA190_0 >= IDENT && LA190_0 <= INTEGER)||(LA190_0 >= K_AGGREGATE && LA190_0 <= K_ALL)||LA190_0==K_AS||LA190_0==K_ASCII||(LA190_0 >= K_BIGINT && LA190_0 <= K_BOOLEAN)||(LA190_0 >= K_CALLED && LA190_0 <= K_CLUSTERING)||(LA190_0 >= K_COMPACT && LA190_0 <= K_COUNTER)||LA190_0==K_CUSTOM||(LA190_0 >= K_DATE && LA190_0 <= K_DECIMAL)||(LA190_0 >= K_DISTINCT && LA190_0 <= K_DOUBLE)||LA190_0==K_DURATION||(LA190_0 >= K_EXISTS && LA190_0 <= K_FLOAT)||LA190_0==K_FROZEN||(LA190_0 >= K_FUNCTION && LA190_0 <= K_FUNCTIONS)||LA190_0==K_GROUP||(LA190_0 >= K_INET && LA190_0 <= K_INPUT)||LA190_0==K_INT||(LA190_0 >= K_JSON && LA190_0 <= K_KEYS)||(LA190_0 >= K_KEYSPACES && LA190_0 <= K_LIKE)||(LA190_0 >= K_LIST && LA190_0 <= K_MAP)||(LA190_0 >= K_NEGATIVE_INFINITY && LA190_0 <= K_NOLOGIN)||LA190_0==K_NOSUPERUSER||LA190_0==K_NULL||LA190_0==K_OPTIONS||(LA190_0 >= K_PARTITION && LA190_0 <= K_POSITIVE_NAN)||LA190_0==K_RETURNS||(LA190_0 >= K_ROLE && LA190_0 <= K_ROLES)||(LA190_0 >= K_SFUNC && LA190_0 <= K_TINYINT)||(LA190_0 >= K_TOKEN && LA190_0 <= K_TRIGGER)||(LA190_0 >= K_TTL && LA190_0 <= K_TYPE)||(LA190_0 >= K_USER && LA190_0 <= K_USERS)||(LA190_0 >= K_UUID && LA190_0 <= K_VARINT)||LA190_0==K_WRITETIME||(LA190_0 >= QMARK && LA190_0 <= QUOTED_NAME)||LA190_0==STRING_LITERAL||LA190_0==UUID||LA190_0==190||LA190_0==195||LA190_0==199||LA190_0==206||LA190_0==210) ) {
				alt190=1;
			}
			switch (alt190) {
				case 1 :
					// Parser.g:1445:13: t1= term ( ',' tn= term )*
					{
					pushFollow(FOLLOW_term_in_listLiteral10248);
					t1=term();
					state._fsp--;
					if (state.failed) return value;
					if ( state.backtracking==0 ) { l.add(t1); }
					// Parser.g:1445:36: ( ',' tn= term )*
					loop189:
					while (true) {
						int alt189=2;
						int LA189_0 = input.LA(1);
						if ( (LA189_0==194) ) {
							alt189=1;
						}

						switch (alt189) {
						case 1 :
							// Parser.g:1445:38: ',' tn= term
							{
							match(input,194,FOLLOW_194_in_listLiteral10254); if (state.failed) return value;
							pushFollow(FOLLOW_term_in_listLiteral10258);
							tn=term();
							state._fsp--;
							if (state.failed) return value;
							if ( state.backtracking==0 ) { l.add(tn); }
							}
							break;

						default :
							break loop189;
						}
					}

					}
					break;

			}

			match(input,208,FOLLOW_208_in_listLiteral10268); if (state.failed) return value;
			if ( state.backtracking==0 ) { value = new Lists.Literal(l); }
			}

			if ( state.backtracking==0 ) {value = new Lists.Literal(l);}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return value;
	}
	// $ANTLR end "listLiteral"



	// $ANTLR start "usertypeLiteral"
	// Parser.g:1448:1: usertypeLiteral returns [UserTypes.Literal ut] : '{' k1= fident ':' v1= term ( ',' kn= fident ':' vn= term )* '}' ;
	public final UserTypes.Literal usertypeLiteral() throws RecognitionException {
		UserTypes.Literal ut = null;


		FieldIdentifier k1 =null;
		Term.Raw v1 =null;
		FieldIdentifier kn =null;
		Term.Raw vn =null;

		 Map<FieldIdentifier, Term.Raw> m = new HashMap<>(); 
		try {
			// Parser.g:1452:5: ( '{' k1= fident ':' v1= term ( ',' kn= fident ':' vn= term )* '}' )
			// Parser.g:1452:7: '{' k1= fident ':' v1= term ( ',' kn= fident ':' vn= term )* '}'
			{
			match(input,210,FOLLOW_210_in_usertypeLiteral10312); if (state.failed) return ut;
			pushFollow(FOLLOW_fident_in_usertypeLiteral10316);
			k1=fident();
			state._fsp--;
			if (state.failed) return ut;
			match(input,199,FOLLOW_199_in_usertypeLiteral10318); if (state.failed) return ut;
			pushFollow(FOLLOW_term_in_usertypeLiteral10322);
			v1=term();
			state._fsp--;
			if (state.failed) return ut;
			if ( state.backtracking==0 ) { m.put(k1, v1); }
			// Parser.g:1452:52: ( ',' kn= fident ':' vn= term )*
			loop191:
			while (true) {
				int alt191=2;
				int LA191_0 = input.LA(1);
				if ( (LA191_0==194) ) {
					alt191=1;
				}

				switch (alt191) {
				case 1 :
					// Parser.g:1452:54: ',' kn= fident ':' vn= term
					{
					match(input,194,FOLLOW_194_in_usertypeLiteral10328); if (state.failed) return ut;
					pushFollow(FOLLOW_fident_in_usertypeLiteral10332);
					kn=fident();
					state._fsp--;
					if (state.failed) return ut;
					match(input,199,FOLLOW_199_in_usertypeLiteral10334); if (state.failed) return ut;
					pushFollow(FOLLOW_term_in_usertypeLiteral10338);
					vn=term();
					state._fsp--;
					if (state.failed) return ut;
					if ( state.backtracking==0 ) { m.put(kn, vn); }
					}
					break;

				default :
					break loop191;
				}
			}

			match(input,211,FOLLOW_211_in_usertypeLiteral10345); if (state.failed) return ut;
			}

			if ( state.backtracking==0 ) { ut = new UserTypes.Literal(m); }
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return ut;
	}
	// $ANTLR end "usertypeLiteral"



	// $ANTLR start "tupleLiteral"
	// Parser.g:1455:1: tupleLiteral returns [Tuples.Literal tt] : '(' t1= term ( ',' tn= term )* ')' ;
	public final Tuples.Literal tupleLiteral() throws RecognitionException {
		Tuples.Literal tt = null;


		Term.Raw t1 =null;
		Term.Raw tn =null;

		 List<Term.Raw> l = new ArrayList<Term.Raw>(); 
		try {
			// Parser.g:1458:5: ( '(' t1= term ( ',' tn= term )* ')' )
			// Parser.g:1458:7: '(' t1= term ( ',' tn= term )* ')'
			{
			match(input,190,FOLLOW_190_in_tupleLiteral10382); if (state.failed) return tt;
			pushFollow(FOLLOW_term_in_tupleLiteral10386);
			t1=term();
			state._fsp--;
			if (state.failed) return tt;
			if ( state.backtracking==0 ) { l.add(t1); }
			// Parser.g:1458:34: ( ',' tn= term )*
			loop192:
			while (true) {
				int alt192=2;
				int LA192_0 = input.LA(1);
				if ( (LA192_0==194) ) {
					alt192=1;
				}

				switch (alt192) {
				case 1 :
					// Parser.g:1458:36: ',' tn= term
					{
					match(input,194,FOLLOW_194_in_tupleLiteral10392); if (state.failed) return tt;
					pushFollow(FOLLOW_term_in_tupleLiteral10396);
					tn=term();
					state._fsp--;
					if (state.failed) return tt;
					if ( state.backtracking==0 ) { l.add(tn); }
					}
					break;

				default :
					break loop192;
				}
			}

			match(input,191,FOLLOW_191_in_tupleLiteral10403); if (state.failed) return tt;
			}

			if ( state.backtracking==0 ) { tt = new Tuples.Literal(l); }
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return tt;
	}
	// $ANTLR end "tupleLiteral"



	// $ANTLR start "value"
	// Parser.g:1461:1: value returns [Term.Raw value] : (c= constant |l= collectionLiteral |u= usertypeLiteral |t= tupleLiteral | K_NULL | ':' id= noncol_ident | QMARK );
	public final Term.Raw value() throws RecognitionException {
		Term.Raw value = null;


		Constants.Literal c =null;
		Term.Raw l =null;
		UserTypes.Literal u =null;
		Tuples.Literal t =null;
		ColumnIdentifier id =null;

		try {
			// Parser.g:1462:5: (c= constant |l= collectionLiteral |u= usertypeLiteral |t= tupleLiteral | K_NULL | ':' id= noncol_ident | QMARK )
			int alt193=7;
			alt193 = dfa193.predict(input);
			switch (alt193) {
				case 1 :
					// Parser.g:1462:7: c= constant
					{
					pushFollow(FOLLOW_constant_in_value10426);
					c=constant();
					state._fsp--;
					if (state.failed) return value;
					if ( state.backtracking==0 ) { value = c; }
					}
					break;
				case 2 :
					// Parser.g:1463:7: l= collectionLiteral
					{
					pushFollow(FOLLOW_collectionLiteral_in_value10448);
					l=collectionLiteral();
					state._fsp--;
					if (state.failed) return value;
					if ( state.backtracking==0 ) { value = l; }
					}
					break;
				case 3 :
					// Parser.g:1464:7: u= usertypeLiteral
					{
					pushFollow(FOLLOW_usertypeLiteral_in_value10461);
					u=usertypeLiteral();
					state._fsp--;
					if (state.failed) return value;
					if ( state.backtracking==0 ) { value = u; }
					}
					break;
				case 4 :
					// Parser.g:1465:7: t= tupleLiteral
					{
					pushFollow(FOLLOW_tupleLiteral_in_value10476);
					t=tupleLiteral();
					state._fsp--;
					if (state.failed) return value;
					if ( state.backtracking==0 ) { value = t; }
					}
					break;
				case 5 :
					// Parser.g:1466:7: K_NULL
					{
					match(input,K_NULL,FOLLOW_K_NULL_in_value10492); if (state.failed) return value;
					if ( state.backtracking==0 ) { value = Constants.NULL_LITERAL; }
					}
					break;
				case 6 :
					// Parser.g:1467:7: ':' id= noncol_ident
					{
					match(input,199,FOLLOW_199_in_value10516); if (state.failed) return value;
					pushFollow(FOLLOW_noncol_ident_in_value10520);
					id=noncol_ident();
					state._fsp--;
					if (state.failed) return value;
					if ( state.backtracking==0 ) { value = newBindVariables(id); }
					}
					break;
				case 7 :
					// Parser.g:1468:7: QMARK
					{
					match(input,QMARK,FOLLOW_QMARK_in_value10531); if (state.failed) return value;
					if ( state.backtracking==0 ) { value = newBindVariables(null); }
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return value;
	}
	// $ANTLR end "value"



	// $ANTLR start "intValue"
	// Parser.g:1471:1: intValue returns [Term.Raw value] : (t= INTEGER | ':' id= noncol_ident | QMARK );
	public final Term.Raw intValue() throws RecognitionException {
		Term.Raw value = null;


		Token t=null;
		ColumnIdentifier id =null;

		try {
			// Parser.g:1472:5: (t= INTEGER | ':' id= noncol_ident | QMARK )
			int alt194=3;
			switch ( input.LA(1) ) {
			case INTEGER:
				{
				alt194=1;
				}
				break;
			case 199:
				{
				alt194=2;
				}
				break;
			case QMARK:
				{
				alt194=3;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return value;}
				NoViableAltException nvae =
					new NoViableAltException("", 194, 0, input);
				throw nvae;
			}
			switch (alt194) {
				case 1 :
					// Parser.g:1472:7: t= INTEGER
					{
					t=(Token)match(input,INTEGER,FOLLOW_INTEGER_in_intValue10571); if (state.failed) return value;
					if ( state.backtracking==0 ) { value = Constants.Literal.integer((t!=null?t.getText():null)); }
					}
					break;
				case 2 :
					// Parser.g:1473:7: ':' id= noncol_ident
					{
					match(input,199,FOLLOW_199_in_intValue10585); if (state.failed) return value;
					pushFollow(FOLLOW_noncol_ident_in_intValue10589);
					id=noncol_ident();
					state._fsp--;
					if (state.failed) return value;
					if ( state.backtracking==0 ) { value = newBindVariables(id); }
					}
					break;
				case 3 :
					// Parser.g:1474:7: QMARK
					{
					match(input,QMARK,FOLLOW_QMARK_in_intValue10600); if (state.failed) return value;
					if ( state.backtracking==0 ) { value = newBindVariables(null); }
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return value;
	}
	// $ANTLR end "intValue"



	// $ANTLR start "functionName"
	// Parser.g:1477:1: functionName returns [FunctionName s] : (ks= keyspaceName '.' )? f= allowedFunctionName ;
	public final FunctionName functionName() throws RecognitionException {
		FunctionName s = null;


		String ks =null;
		String f =null;

		try {
			// Parser.g:1480:5: ( (ks= keyspaceName '.' )? f= allowedFunctionName )
			// Parser.g:1480:7: (ks= keyspaceName '.' )? f= allowedFunctionName
			{
			// Parser.g:1480:7: (ks= keyspaceName '.' )?
			int alt195=2;
			alt195 = dfa195.predict(input);
			switch (alt195) {
				case 1 :
					// Parser.g:1480:8: ks= keyspaceName '.'
					{
					pushFollow(FOLLOW_keyspaceName_in_functionName10646);
					ks=keyspaceName();
					state._fsp--;
					if (state.failed) return s;
					match(input,197,FOLLOW_197_in_functionName10648); if (state.failed) return s;
					}
					break;

			}

			pushFollow(FOLLOW_allowedFunctionName_in_functionName10654);
			f=allowedFunctionName();
			state._fsp--;
			if (state.failed) return s;
			if ( state.backtracking==0 ) { s = f == null ? null : new FunctionName(ks, f); }
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return s;
	}
	// $ANTLR end "functionName"



	// $ANTLR start "allowedFunctionName"
	// Parser.g:1483:1: allowedFunctionName returns [String s] : (f= IDENT |f= QUOTED_NAME |u= unreserved_function_keyword | K_TOKEN | K_COUNT );
	public final String allowedFunctionName() throws RecognitionException {
		String s = null;


		Token f=null;
		String u =null;

		try {
			// Parser.g:1484:5: (f= IDENT |f= QUOTED_NAME |u= unreserved_function_keyword | K_TOKEN | K_COUNT )
			int alt196=5;
			switch ( input.LA(1) ) {
			case IDENT:
				{
				alt196=1;
				}
				break;
			case QUOTED_NAME:
				{
				alt196=2;
				}
				break;
			case K_AGGREGATE:
			case K_ALL:
			case K_AS:
			case K_ASCII:
			case K_BIGINT:
			case K_BLOB:
			case K_BOOLEAN:
			case K_CALLED:
			case K_CLUSTERING:
			case K_COMPACT:
			case K_CONTAINS:
			case K_COUNTER:
			case K_CUSTOM:
			case K_DATE:
			case K_DECIMAL:
			case K_DOUBLE:
			case K_DURATION:
			case K_EXISTS:
			case K_FILTERING:
			case K_FINALFUNC:
			case K_FLOAT:
			case K_FROZEN:
			case K_FUNCTION:
			case K_FUNCTIONS:
			case K_GROUP:
			case K_INET:
			case K_INITCOND:
			case K_INPUT:
			case K_INT:
			case K_KEYS:
			case K_KEYSPACES:
			case K_LANGUAGE:
			case K_LIKE:
			case K_LIST:
			case K_LOGIN:
			case K_MAP:
			case K_NOLOGIN:
			case K_NOSUPERUSER:
			case K_OPTIONS:
			case K_PARTITION:
			case K_PASSWORD:
			case K_PER:
			case K_PERMISSION:
			case K_PERMISSIONS:
			case K_RETURNS:
			case K_ROLE:
			case K_ROLES:
			case K_SFUNC:
			case K_SMALLINT:
			case K_STATIC:
			case K_STORAGE:
			case K_STYPE:
			case K_SUPERUSER:
			case K_TEXT:
			case K_TIME:
			case K_TIMESTAMP:
			case K_TIMEUUID:
			case K_TINYINT:
			case K_TRIGGER:
			case K_TUPLE:
			case K_TYPE:
			case K_USER:
			case K_USERS:
			case K_UUID:
			case K_VALUES:
			case K_VARCHAR:
			case K_VARINT:
				{
				alt196=3;
				}
				break;
			case K_TOKEN:
				{
				alt196=4;
				}
				break;
			case K_COUNT:
				{
				alt196=5;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return s;}
				NoViableAltException nvae =
					new NoViableAltException("", 196, 0, input);
				throw nvae;
			}
			switch (alt196) {
				case 1 :
					// Parser.g:1484:7: f= IDENT
					{
					f=(Token)match(input,IDENT,FOLLOW_IDENT_in_allowedFunctionName10681); if (state.failed) return s;
					if ( state.backtracking==0 ) { s = (f!=null?f.getText():null).toLowerCase(); }
					}
					break;
				case 2 :
					// Parser.g:1485:7: f= QUOTED_NAME
					{
					f=(Token)match(input,QUOTED_NAME,FOLLOW_QUOTED_NAME_in_allowedFunctionName10715); if (state.failed) return s;
					if ( state.backtracking==0 ) { s = (f!=null?f.getText():null); }
					}
					break;
				case 3 :
					// Parser.g:1486:7: u= unreserved_function_keyword
					{
					pushFollow(FOLLOW_unreserved_function_keyword_in_allowedFunctionName10743);
					u=unreserved_function_keyword();
					state._fsp--;
					if (state.failed) return s;
					if ( state.backtracking==0 ) { s = u; }
					}
					break;
				case 4 :
					// Parser.g:1487:7: K_TOKEN
					{
					match(input,K_TOKEN,FOLLOW_K_TOKEN_in_allowedFunctionName10753); if (state.failed) return s;
					if ( state.backtracking==0 ) { s = "token"; }
					}
					break;
				case 5 :
					// Parser.g:1488:7: K_COUNT
					{
					match(input,K_COUNT,FOLLOW_K_COUNT_in_allowedFunctionName10785); if (state.failed) return s;
					if ( state.backtracking==0 ) { s = "count"; }
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return s;
	}
	// $ANTLR end "allowedFunctionName"



	// $ANTLR start "function"
	// Parser.g:1491:1: function returns [Term.Raw t] : (f= functionName '(' ')' |f= functionName '(' args= functionArgs ')' );
	public final Term.Raw function() throws RecognitionException {
		Term.Raw t = null;


		FunctionName f =null;
		List<Term.Raw> args =null;

		try {
			// Parser.g:1492:5: (f= functionName '(' ')' |f= functionName '(' args= functionArgs ')' )
			int alt197=2;
			alt197 = dfa197.predict(input);
			switch (alt197) {
				case 1 :
					// Parser.g:1492:7: f= functionName '(' ')'
					{
					pushFollow(FOLLOW_functionName_in_function10832);
					f=functionName();
					state._fsp--;
					if (state.failed) return t;
					match(input,190,FOLLOW_190_in_function10834); if (state.failed) return t;
					match(input,191,FOLLOW_191_in_function10836); if (state.failed) return t;
					if ( state.backtracking==0 ) { t = new FunctionCall.Raw(f, Collections.<Term.Raw>emptyList()); }
					}
					break;
				case 2 :
					// Parser.g:1493:7: f= functionName '(' args= functionArgs ')'
					{
					pushFollow(FOLLOW_functionName_in_function10866);
					f=functionName();
					state._fsp--;
					if (state.failed) return t;
					match(input,190,FOLLOW_190_in_function10868); if (state.failed) return t;
					pushFollow(FOLLOW_functionArgs_in_function10872);
					args=functionArgs();
					state._fsp--;
					if (state.failed) return t;
					match(input,191,FOLLOW_191_in_function10874); if (state.failed) return t;
					if ( state.backtracking==0 ) { t = new FunctionCall.Raw(f, args); }
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return t;
	}
	// $ANTLR end "function"



	// $ANTLR start "functionArgs"
	// Parser.g:1496:1: functionArgs returns [List<Term.Raw> args] : t1= term ( ',' tn= term )* ;
	public final List<Term.Raw> functionArgs() throws RecognitionException {
		List<Term.Raw> args = null;


		Term.Raw t1 =null;
		Term.Raw tn =null;

		 args = new ArrayList<Term.Raw>(); 
		try {
			// Parser.g:1498:5: (t1= term ( ',' tn= term )* )
			// Parser.g:1498:7: t1= term ( ',' tn= term )*
			{
			pushFollow(FOLLOW_term_in_functionArgs10907);
			t1=term();
			state._fsp--;
			if (state.failed) return args;
			if ( state.backtracking==0 ) {args.add(t1); }
			// Parser.g:1498:32: ( ',' tn= term )*
			loop198:
			while (true) {
				int alt198=2;
				int LA198_0 = input.LA(1);
				if ( (LA198_0==194) ) {
					alt198=1;
				}

				switch (alt198) {
				case 1 :
					// Parser.g:1498:34: ',' tn= term
					{
					match(input,194,FOLLOW_194_in_functionArgs10913); if (state.failed) return args;
					pushFollow(FOLLOW_term_in_functionArgs10917);
					tn=term();
					state._fsp--;
					if (state.failed) return args;
					if ( state.backtracking==0 ) { args.add(tn); }
					}
					break;

				default :
					break loop198;
				}
			}

			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return args;
	}
	// $ANTLR end "functionArgs"



	// $ANTLR start "term"
	// Parser.g:1501:1: term returns [Term.Raw term] : t= termAddition ;
	public final Term.Raw term() throws RecognitionException {
		Term.Raw term = null;


		Term.Raw t =null;

		try {
			// Parser.g:1502:5: (t= termAddition )
			// Parser.g:1502:7: t= termAddition
			{
			pushFollow(FOLLOW_termAddition_in_term10945);
			t=termAddition();
			state._fsp--;
			if (state.failed) return term;
			if ( state.backtracking==0 ) { term = t; }
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return term;
	}
	// $ANTLR end "term"



	// $ANTLR start "termAddition"
	// Parser.g:1505:1: termAddition returns [Term.Raw term] : l= termMultiplication ( '+' r= termMultiplication | '-' r= termMultiplication )* ;
	public final Term.Raw termAddition() throws RecognitionException {
		Term.Raw term = null;


		Term.Raw l =null;
		Term.Raw r =null;

		try {
			// Parser.g:1506:5: (l= termMultiplication ( '+' r= termMultiplication | '-' r= termMultiplication )* )
			// Parser.g:1506:9: l= termMultiplication ( '+' r= termMultiplication | '-' r= termMultiplication )*
			{
			pushFollow(FOLLOW_termMultiplication_in_termAddition10997);
			l=termMultiplication();
			state._fsp--;
			if (state.failed) return term;
			if ( state.backtracking==0 ) {term = l;}
			// Parser.g:1507:9: ( '+' r= termMultiplication | '-' r= termMultiplication )*
			loop199:
			while (true) {
				int alt199=3;
				alt199 = dfa199.predict(input);
				switch (alt199) {
				case 1 :
					// Parser.g:1507:11: '+' r= termMultiplication
					{
					match(input,192,FOLLOW_192_in_termAddition11013); if (state.failed) return term;
					pushFollow(FOLLOW_termMultiplication_in_termAddition11017);
					r=termMultiplication();
					state._fsp--;
					if (state.failed) return term;
					if ( state.backtracking==0 ) {term = FunctionCall.Raw.newOperation('+', term, r);}
					}
					break;
				case 2 :
					// Parser.g:1508:11: '-' r= termMultiplication
					{
					match(input,195,FOLLOW_195_in_termAddition11031); if (state.failed) return term;
					pushFollow(FOLLOW_termMultiplication_in_termAddition11035);
					r=termMultiplication();
					state._fsp--;
					if (state.failed) return term;
					if ( state.backtracking==0 ) {term = FunctionCall.Raw.newOperation('-', term, r);}
					}
					break;

				default :
					break loop199;
				}
			}

			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return term;
	}
	// $ANTLR end "termAddition"



	// $ANTLR start "termMultiplication"
	// Parser.g:1512:1: termMultiplication returns [Term.Raw term] : l= termGroup ( '\\*' r= termGroup | '/' r= termGroup | '%' r= termGroup )* ;
	public final Term.Raw termMultiplication() throws RecognitionException {
		Term.Raw term = null;


		Term.Raw l =null;
		Term.Raw r =null;

		try {
			// Parser.g:1513:5: (l= termGroup ( '\\*' r= termGroup | '/' r= termGroup | '%' r= termGroup )* )
			// Parser.g:1513:9: l= termGroup ( '\\*' r= termGroup | '/' r= termGroup | '%' r= termGroup )*
			{
			pushFollow(FOLLOW_termGroup_in_termMultiplication11073);
			l=termGroup();
			state._fsp--;
			if (state.failed) return term;
			if ( state.backtracking==0 ) {term = l;}
			// Parser.g:1514:9: ( '\\*' r= termGroup | '/' r= termGroup | '%' r= termGroup )*
			loop200:
			while (true) {
				int alt200=4;
				switch ( input.LA(1) ) {
				case 207:
					{
					alt200=1;
					}
					break;
				case 198:
					{
					alt200=2;
					}
					break;
				case 189:
					{
					alt200=3;
					}
					break;
				}
				switch (alt200) {
				case 1 :
					// Parser.g:1514:11: '\\*' r= termGroup
					{
					match(input,207,FOLLOW_207_in_termMultiplication11089); if (state.failed) return term;
					pushFollow(FOLLOW_termGroup_in_termMultiplication11093);
					r=termGroup();
					state._fsp--;
					if (state.failed) return term;
					if ( state.backtracking==0 ) {term = FunctionCall.Raw.newOperation('*', term, r);}
					}
					break;
				case 2 :
					// Parser.g:1515:11: '/' r= termGroup
					{
					match(input,198,FOLLOW_198_in_termMultiplication11107); if (state.failed) return term;
					pushFollow(FOLLOW_termGroup_in_termMultiplication11111);
					r=termGroup();
					state._fsp--;
					if (state.failed) return term;
					if ( state.backtracking==0 ) {term = FunctionCall.Raw.newOperation('/', term, r);}
					}
					break;
				case 3 :
					// Parser.g:1516:11: '%' r= termGroup
					{
					match(input,189,FOLLOW_189_in_termMultiplication11125); if (state.failed) return term;
					pushFollow(FOLLOW_termGroup_in_termMultiplication11129);
					r=termGroup();
					state._fsp--;
					if (state.failed) return term;
					if ( state.backtracking==0 ) {term = FunctionCall.Raw.newOperation('%', term, r);}
					}
					break;

				default :
					break loop200;
				}
			}

			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return term;
	}
	// $ANTLR end "termMultiplication"



	// $ANTLR start "termGroup"
	// Parser.g:1520:1: termGroup returns [Term.Raw term] : (t= simpleTerm | '-' t= simpleTerm );
	public final Term.Raw termGroup() throws RecognitionException {
		Term.Raw term = null;


		Term.Raw t =null;

		try {
			// Parser.g:1521:5: (t= simpleTerm | '-' t= simpleTerm )
			int alt201=2;
			int LA201_0 = input.LA(1);
			if ( (LA201_0==BOOLEAN||LA201_0==DURATION||LA201_0==FLOAT||LA201_0==HEXNUMBER||(LA201_0 >= IDENT && LA201_0 <= INTEGER)||(LA201_0 >= K_AGGREGATE && LA201_0 <= K_ALL)||LA201_0==K_AS||LA201_0==K_ASCII||(LA201_0 >= K_BIGINT && LA201_0 <= K_BOOLEAN)||(LA201_0 >= K_CALLED && LA201_0 <= K_CLUSTERING)||(LA201_0 >= K_COMPACT && LA201_0 <= K_COUNTER)||LA201_0==K_CUSTOM||(LA201_0 >= K_DATE && LA201_0 <= K_DECIMAL)||(LA201_0 >= K_DISTINCT && LA201_0 <= K_DOUBLE)||LA201_0==K_DURATION||(LA201_0 >= K_EXISTS && LA201_0 <= K_FLOAT)||LA201_0==K_FROZEN||(LA201_0 >= K_FUNCTION && LA201_0 <= K_FUNCTIONS)||LA201_0==K_GROUP||(LA201_0 >= K_INET && LA201_0 <= K_INPUT)||LA201_0==K_INT||(LA201_0 >= K_JSON && LA201_0 <= K_KEYS)||(LA201_0 >= K_KEYSPACES && LA201_0 <= K_LIKE)||(LA201_0 >= K_LIST && LA201_0 <= K_MAP)||(LA201_0 >= K_NEGATIVE_INFINITY && LA201_0 <= K_NOLOGIN)||LA201_0==K_NOSUPERUSER||LA201_0==K_NULL||LA201_0==K_OPTIONS||(LA201_0 >= K_PARTITION && LA201_0 <= K_POSITIVE_NAN)||LA201_0==K_RETURNS||(LA201_0 >= K_ROLE && LA201_0 <= K_ROLES)||(LA201_0 >= K_SFUNC && LA201_0 <= K_TINYINT)||(LA201_0 >= K_TOKEN && LA201_0 <= K_TRIGGER)||(LA201_0 >= K_TTL && LA201_0 <= K_TYPE)||(LA201_0 >= K_USER && LA201_0 <= K_USERS)||(LA201_0 >= K_UUID && LA201_0 <= K_VARINT)||LA201_0==K_WRITETIME||(LA201_0 >= QMARK && LA201_0 <= QUOTED_NAME)||LA201_0==STRING_LITERAL||LA201_0==UUID||LA201_0==190||LA201_0==199||LA201_0==206||LA201_0==210) ) {
				alt201=1;
			}
			else if ( (LA201_0==195) ) {
				alt201=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return term;}
				NoViableAltException nvae =
					new NoViableAltException("", 201, 0, input);
				throw nvae;
			}

			switch (alt201) {
				case 1 :
					// Parser.g:1521:7: t= simpleTerm
					{
					pushFollow(FOLLOW_simpleTerm_in_termGroup11165);
					t=simpleTerm();
					state._fsp--;
					if (state.failed) return term;
					if ( state.backtracking==0 ) { term = t; }
					}
					break;
				case 2 :
					// Parser.g:1522:7: '-' t= simpleTerm
					{
					match(input,195,FOLLOW_195_in_termGroup11188); if (state.failed) return term;
					pushFollow(FOLLOW_simpleTerm_in_termGroup11193);
					t=simpleTerm();
					state._fsp--;
					if (state.failed) return term;
					if ( state.backtracking==0 ) { term = FunctionCall.Raw.newNegation(t); }
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return term;
	}
	// $ANTLR end "termGroup"



	// $ANTLR start "simpleTerm"
	// Parser.g:1525:1: simpleTerm returns [Term.Raw term] : (v= value |f= function | '(' c= comparatorType ')' t= simpleTerm );
	public final Term.Raw simpleTerm() throws RecognitionException {
		Term.Raw term = null;


		Term.Raw v =null;
		Term.Raw f =null;
		CQL3Type.Raw c =null;
		Term.Raw t =null;

		try {
			// Parser.g:1526:5: (v= value |f= function | '(' c= comparatorType ')' t= simpleTerm )
			int alt202=3;
			alt202 = dfa202.predict(input);
			switch (alt202) {
				case 1 :
					// Parser.g:1526:7: v= value
					{
					pushFollow(FOLLOW_value_in_simpleTerm11226);
					v=value();
					state._fsp--;
					if (state.failed) return term;
					if ( state.backtracking==0 ) { term = v; }
					}
					break;
				case 2 :
					// Parser.g:1527:7: f= function
					{
					pushFollow(FOLLOW_function_in_simpleTerm11270);
					f=function();
					state._fsp--;
					if (state.failed) return term;
					if ( state.backtracking==0 ) { term = f; }
					}
					break;
				case 3 :
					// Parser.g:1528:7: '(' c= comparatorType ')' t= simpleTerm
					{
					match(input,190,FOLLOW_190_in_simpleTerm11309); if (state.failed) return term;
					pushFollow(FOLLOW_comparatorType_in_simpleTerm11313);
					c=comparatorType();
					state._fsp--;
					if (state.failed) return term;
					match(input,191,FOLLOW_191_in_simpleTerm11315); if (state.failed) return term;
					pushFollow(FOLLOW_simpleTerm_in_simpleTerm11319);
					t=simpleTerm();
					state._fsp--;
					if (state.failed) return term;
					if ( state.backtracking==0 ) { term = new TypeCast(c, t); }
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return term;
	}
	// $ANTLR end "simpleTerm"



	// $ANTLR start "columnOperation"
	// Parser.g:1531:1: columnOperation[List<Pair<ColumnMetadata.Raw, Operation.RawUpdate>> operations] : key= cident columnOperationDifferentiator[operations, key] ;
	public final void columnOperation(List<Pair<ColumnMetadata.Raw, Operation.RawUpdate>> operations) throws RecognitionException {
		ColumnMetadata.Raw key =null;

		try {
			// Parser.g:1532:5: (key= cident columnOperationDifferentiator[operations, key] )
			// Parser.g:1532:7: key= cident columnOperationDifferentiator[operations, key]
			{
			pushFollow(FOLLOW_cident_in_columnOperation11343);
			key=cident();
			state._fsp--;
			if (state.failed) return;
			pushFollow(FOLLOW_columnOperationDifferentiator_in_columnOperation11345);
			columnOperationDifferentiator(operations, key);
			state._fsp--;
			if (state.failed) return;
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "columnOperation"



	// $ANTLR start "columnOperationDifferentiator"
	// Parser.g:1535:1: columnOperationDifferentiator[List<Pair<ColumnMetadata.Raw, Operation.RawUpdate>> operations, ColumnMetadata.Raw key] : ( '=' normalColumnOperation[operations, key] | shorthandColumnOperation[operations, key] | '[' k= term ']' collectionColumnOperation[operations, key, k] | '.' field= fident udtColumnOperation[operations, key, field] );
	public final void columnOperationDifferentiator(List<Pair<ColumnMetadata.Raw, Operation.RawUpdate>> operations, ColumnMetadata.Raw key) throws RecognitionException {
		Term.Raw k =null;
		FieldIdentifier field =null;

		try {
			// Parser.g:1536:5: ( '=' normalColumnOperation[operations, key] | shorthandColumnOperation[operations, key] | '[' k= term ']' collectionColumnOperation[operations, key, k] | '.' field= fident udtColumnOperation[operations, key, field] )
			int alt203=4;
			switch ( input.LA(1) ) {
			case 203:
				{
				alt203=1;
				}
				break;
			case 193:
			case 196:
				{
				alt203=2;
				}
				break;
			case 206:
				{
				alt203=3;
				}
				break;
			case 197:
				{
				alt203=4;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return;}
				NoViableAltException nvae =
					new NoViableAltException("", 203, 0, input);
				throw nvae;
			}
			switch (alt203) {
				case 1 :
					// Parser.g:1536:7: '=' normalColumnOperation[operations, key]
					{
					match(input,203,FOLLOW_203_in_columnOperationDifferentiator11364); if (state.failed) return;
					pushFollow(FOLLOW_normalColumnOperation_in_columnOperationDifferentiator11366);
					normalColumnOperation(operations, key);
					state._fsp--;
					if (state.failed) return;
					}
					break;
				case 2 :
					// Parser.g:1537:7: shorthandColumnOperation[operations, key]
					{
					pushFollow(FOLLOW_shorthandColumnOperation_in_columnOperationDifferentiator11375);
					shorthandColumnOperation(operations, key);
					state._fsp--;
					if (state.failed) return;
					}
					break;
				case 3 :
					// Parser.g:1538:7: '[' k= term ']' collectionColumnOperation[operations, key, k]
					{
					match(input,206,FOLLOW_206_in_columnOperationDifferentiator11384); if (state.failed) return;
					pushFollow(FOLLOW_term_in_columnOperationDifferentiator11388);
					k=term();
					state._fsp--;
					if (state.failed) return;
					match(input,208,FOLLOW_208_in_columnOperationDifferentiator11390); if (state.failed) return;
					pushFollow(FOLLOW_collectionColumnOperation_in_columnOperationDifferentiator11392);
					collectionColumnOperation(operations, key, k);
					state._fsp--;
					if (state.failed) return;
					}
					break;
				case 4 :
					// Parser.g:1539:7: '.' field= fident udtColumnOperation[operations, key, field]
					{
					match(input,197,FOLLOW_197_in_columnOperationDifferentiator11401); if (state.failed) return;
					pushFollow(FOLLOW_fident_in_columnOperationDifferentiator11405);
					field=fident();
					state._fsp--;
					if (state.failed) return;
					pushFollow(FOLLOW_udtColumnOperation_in_columnOperationDifferentiator11407);
					udtColumnOperation(operations, key, field);
					state._fsp--;
					if (state.failed) return;
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "columnOperationDifferentiator"



	// $ANTLR start "normalColumnOperation"
	// Parser.g:1542:1: normalColumnOperation[List<Pair<ColumnMetadata.Raw, Operation.RawUpdate>> operations, ColumnMetadata.Raw key] : (t= term ( '+' c= cident )? |c= cident sig= ( '+' | '-' ) t= term |c= cident i= INTEGER );
	public final void normalColumnOperation(List<Pair<ColumnMetadata.Raw, Operation.RawUpdate>> operations, ColumnMetadata.Raw key) throws RecognitionException {
		Token sig=null;
		Token i=null;
		Term.Raw t =null;
		ColumnMetadata.Raw c =null;

		try {
			// Parser.g:1543:5: (t= term ( '+' c= cident )? |c= cident sig= ( '+' | '-' ) t= term |c= cident i= INTEGER )
			int alt205=3;
			alt205 = dfa205.predict(input);
			switch (alt205) {
				case 1 :
					// Parser.g:1543:7: t= term ( '+' c= cident )?
					{
					pushFollow(FOLLOW_term_in_normalColumnOperation11428);
					t=term();
					state._fsp--;
					if (state.failed) return;
					// Parser.g:1543:14: ( '+' c= cident )?
					int alt204=2;
					int LA204_0 = input.LA(1);
					if ( (LA204_0==192) ) {
						alt204=1;
					}
					switch (alt204) {
						case 1 :
							// Parser.g:1543:15: '+' c= cident
							{
							match(input,192,FOLLOW_192_in_normalColumnOperation11431); if (state.failed) return;
							pushFollow(FOLLOW_cident_in_normalColumnOperation11435);
							c=cident();
							state._fsp--;
							if (state.failed) return;
							}
							break;

					}

					if ( state.backtracking==0 ) {
					          if (c == null)
					          {
					              addRawUpdate(operations, key, new Operation.SetValue(t));
					          }
					          else
					          {
					              if (!key.equals(c))
					                  addRecognitionError("Only expressions of the form X = <value> + X are supported.");
					              addRawUpdate(operations, key, new Operation.Prepend(t));
					          }
					      }
					}
					break;
				case 2 :
					// Parser.g:1556:7: c= cident sig= ( '+' | '-' ) t= term
					{
					pushFollow(FOLLOW_cident_in_normalColumnOperation11456);
					c=cident();
					state._fsp--;
					if (state.failed) return;
					sig=input.LT(1);
					if ( input.LA(1)==192||input.LA(1)==195 ) {
						input.consume();
						state.errorRecovery=false;
						state.failed=false;
					}
					else {
						if (state.backtracking>0) {state.failed=true; return;}
						MismatchedSetException mse = new MismatchedSetException(null,input);
						throw mse;
					}
					pushFollow(FOLLOW_term_in_normalColumnOperation11470);
					t=term();
					state._fsp--;
					if (state.failed) return;
					if ( state.backtracking==0 ) {
					          if (!key.equals(c))
					              addRecognitionError("Only expressions of the form X = X " + (sig!=null?sig.getText():null) + "<value> are supported.");
					          addRawUpdate(operations, key, (sig!=null?sig.getText():null).equals("+") ? new Operation.Addition(t) : new Operation.Substraction(t));
					      }
					}
					break;
				case 3 :
					// Parser.g:1562:7: c= cident i= INTEGER
					{
					pushFollow(FOLLOW_cident_in_normalColumnOperation11488);
					c=cident();
					state._fsp--;
					if (state.failed) return;
					i=(Token)match(input,INTEGER,FOLLOW_INTEGER_in_normalColumnOperation11492); if (state.failed) return;
					if ( state.backtracking==0 ) {
					          // Note that this production *is* necessary because X = X - 3 will in fact be lexed as [ X, '=', X, INTEGER].
					          if (!key.equals(c))
					              // We don't yet allow a '+' in front of an integer, but we could in the future really, so let's be future-proof in our error message
					              addRecognitionError("Only expressions of the form X = X " + ((i!=null?i.getText():null).charAt(0) == '-' ? '-' : '+') + " <value> are supported.");
					          addRawUpdate(operations, key, new Operation.Addition(Constants.Literal.integer((i!=null?i.getText():null))));
					      }
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "normalColumnOperation"



	// $ANTLR start "shorthandColumnOperation"
	// Parser.g:1572:1: shorthandColumnOperation[List<Pair<ColumnMetadata.Raw, Operation.RawUpdate>> operations, ColumnMetadata.Raw key] : sig= ( '+=' | '-=' ) t= term ;
	public final void shorthandColumnOperation(List<Pair<ColumnMetadata.Raw, Operation.RawUpdate>> operations, ColumnMetadata.Raw key) throws RecognitionException {
		Token sig=null;
		Term.Raw t =null;

		try {
			// Parser.g:1573:5: (sig= ( '+=' | '-=' ) t= term )
			// Parser.g:1573:7: sig= ( '+=' | '-=' ) t= term
			{
			sig=input.LT(1);
			if ( input.LA(1)==193||input.LA(1)==196 ) {
				input.consume();
				state.errorRecovery=false;
				state.failed=false;
			}
			else {
				if (state.backtracking>0) {state.failed=true; return;}
				MismatchedSetException mse = new MismatchedSetException(null,input);
				throw mse;
			}
			pushFollow(FOLLOW_term_in_shorthandColumnOperation11530);
			t=term();
			state._fsp--;
			if (state.failed) return;
			if ( state.backtracking==0 ) {
			          addRawUpdate(operations, key, (sig!=null?sig.getText():null).equals("+=") ? new Operation.Addition(t) : new Operation.Substraction(t));
			      }
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "shorthandColumnOperation"



	// $ANTLR start "collectionColumnOperation"
	// Parser.g:1579:1: collectionColumnOperation[List<Pair<ColumnMetadata.Raw, Operation.RawUpdate>> operations, ColumnMetadata.Raw key, Term.Raw k] : '=' t= term ;
	public final void collectionColumnOperation(List<Pair<ColumnMetadata.Raw, Operation.RawUpdate>> operations, ColumnMetadata.Raw key, Term.Raw k) throws RecognitionException {
		Term.Raw t =null;

		try {
			// Parser.g:1580:5: ( '=' t= term )
			// Parser.g:1580:7: '=' t= term
			{
			match(input,203,FOLLOW_203_in_collectionColumnOperation11556); if (state.failed) return;
			pushFollow(FOLLOW_term_in_collectionColumnOperation11560);
			t=term();
			state._fsp--;
			if (state.failed) return;
			if ( state.backtracking==0 ) {
			          addRawUpdate(operations, key, new Operation.SetElement(k, t));
			      }
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "collectionColumnOperation"



	// $ANTLR start "udtColumnOperation"
	// Parser.g:1586:1: udtColumnOperation[List<Pair<ColumnMetadata.Raw, Operation.RawUpdate>> operations, ColumnMetadata.Raw key, FieldIdentifier field] : '=' t= term ;
	public final void udtColumnOperation(List<Pair<ColumnMetadata.Raw, Operation.RawUpdate>> operations, ColumnMetadata.Raw key, FieldIdentifier field) throws RecognitionException {
		Term.Raw t =null;

		try {
			// Parser.g:1587:5: ( '=' t= term )
			// Parser.g:1587:7: '=' t= term
			{
			match(input,203,FOLLOW_203_in_udtColumnOperation11586); if (state.failed) return;
			pushFollow(FOLLOW_term_in_udtColumnOperation11590);
			t=term();
			state._fsp--;
			if (state.failed) return;
			if ( state.backtracking==0 ) {
			          addRawUpdate(operations, key, new Operation.SetField(field, t));
			      }
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "udtColumnOperation"



	// $ANTLR start "columnCondition"
	// Parser.g:1593:1: columnCondition[List<Pair<ColumnMetadata.Raw, ColumnCondition.Raw>> conditions] : key= cident (op= relationType t= term | K_IN (values= singleColumnInValues |marker= inMarker ) | '[' element= term ']' (op= relationType t= term | K_IN (values= singleColumnInValues |marker= inMarker ) ) | '.' field= fident (op= relationType t= term | K_IN (values= singleColumnInValues |marker= inMarker ) ) ) ;
	public final void columnCondition(List<Pair<ColumnMetadata.Raw, ColumnCondition.Raw>> conditions) throws RecognitionException {
		ColumnMetadata.Raw key =null;
		Operator op =null;
		Term.Raw t =null;
		List<Term.Raw> values =null;
		AbstractMarker.INRaw marker =null;
		Term.Raw element =null;
		FieldIdentifier field =null;

		try {
			// Parser.g:1595:5: (key= cident (op= relationType t= term | K_IN (values= singleColumnInValues |marker= inMarker ) | '[' element= term ']' (op= relationType t= term | K_IN (values= singleColumnInValues |marker= inMarker ) ) | '.' field= fident (op= relationType t= term | K_IN (values= singleColumnInValues |marker= inMarker ) ) ) )
			// Parser.g:1595:7: key= cident (op= relationType t= term | K_IN (values= singleColumnInValues |marker= inMarker ) | '[' element= term ']' (op= relationType t= term | K_IN (values= singleColumnInValues |marker= inMarker ) ) | '.' field= fident (op= relationType t= term | K_IN (values= singleColumnInValues |marker= inMarker ) ) )
			{
			pushFollow(FOLLOW_cident_in_columnCondition11623);
			key=cident();
			state._fsp--;
			if (state.failed) return;
			// Parser.g:1596:9: (op= relationType t= term | K_IN (values= singleColumnInValues |marker= inMarker ) | '[' element= term ']' (op= relationType t= term | K_IN (values= singleColumnInValues |marker= inMarker ) ) | '.' field= fident (op= relationType t= term | K_IN (values= singleColumnInValues |marker= inMarker ) ) )
			int alt211=4;
			switch ( input.LA(1) ) {
			case 188:
			case 201:
			case 202:
			case 203:
			case 204:
			case 205:
				{
				alt211=1;
				}
				break;
			case K_IN:
				{
				alt211=2;
				}
				break;
			case 206:
				{
				alt211=3;
				}
				break;
			case 197:
				{
				alt211=4;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return;}
				NoViableAltException nvae =
					new NoViableAltException("", 211, 0, input);
				throw nvae;
			}
			switch (alt211) {
				case 1 :
					// Parser.g:1596:11: op= relationType t= term
					{
					pushFollow(FOLLOW_relationType_in_columnCondition11637);
					op=relationType();
					state._fsp--;
					if (state.failed) return;
					pushFollow(FOLLOW_term_in_columnCondition11641);
					t=term();
					state._fsp--;
					if (state.failed) return;
					if ( state.backtracking==0 ) { conditions.add(Pair.create(key, ColumnCondition.Raw.simpleCondition(t, op))); }
					}
					break;
				case 2 :
					// Parser.g:1597:11: K_IN (values= singleColumnInValues |marker= inMarker )
					{
					match(input,K_IN,FOLLOW_K_IN_in_columnCondition11655); if (state.failed) return;
					// Parser.g:1598:13: (values= singleColumnInValues |marker= inMarker )
					int alt206=2;
					int LA206_0 = input.LA(1);
					if ( (LA206_0==190) ) {
						alt206=1;
					}
					else if ( (LA206_0==QMARK||LA206_0==199) ) {
						alt206=2;
					}

					else {
						if (state.backtracking>0) {state.failed=true; return;}
						NoViableAltException nvae =
							new NoViableAltException("", 206, 0, input);
						throw nvae;
					}

					switch (alt206) {
						case 1 :
							// Parser.g:1598:15: values= singleColumnInValues
							{
							pushFollow(FOLLOW_singleColumnInValues_in_columnCondition11673);
							values=singleColumnInValues();
							state._fsp--;
							if (state.failed) return;
							if ( state.backtracking==0 ) { conditions.add(Pair.create(key, ColumnCondition.Raw.simpleInCondition(values))); }
							}
							break;
						case 2 :
							// Parser.g:1599:15: marker= inMarker
							{
							pushFollow(FOLLOW_inMarker_in_columnCondition11693);
							marker=inMarker();
							state._fsp--;
							if (state.failed) return;
							if ( state.backtracking==0 ) { conditions.add(Pair.create(key, ColumnCondition.Raw.simpleInCondition(marker))); }
							}
							break;

					}

					}
					break;
				case 3 :
					// Parser.g:1601:11: '[' element= term ']' (op= relationType t= term | K_IN (values= singleColumnInValues |marker= inMarker ) )
					{
					match(input,206,FOLLOW_206_in_columnCondition11721); if (state.failed) return;
					pushFollow(FOLLOW_term_in_columnCondition11725);
					element=term();
					state._fsp--;
					if (state.failed) return;
					match(input,208,FOLLOW_208_in_columnCondition11727); if (state.failed) return;
					// Parser.g:1602:13: (op= relationType t= term | K_IN (values= singleColumnInValues |marker= inMarker ) )
					int alt208=2;
					int LA208_0 = input.LA(1);
					if ( (LA208_0==188||(LA208_0 >= 201 && LA208_0 <= 205)) ) {
						alt208=1;
					}
					else if ( (LA208_0==K_IN) ) {
						alt208=2;
					}

					else {
						if (state.backtracking>0) {state.failed=true; return;}
						NoViableAltException nvae =
							new NoViableAltException("", 208, 0, input);
						throw nvae;
					}

					switch (alt208) {
						case 1 :
							// Parser.g:1602:15: op= relationType t= term
							{
							pushFollow(FOLLOW_relationType_in_columnCondition11745);
							op=relationType();
							state._fsp--;
							if (state.failed) return;
							pushFollow(FOLLOW_term_in_columnCondition11749);
							t=term();
							state._fsp--;
							if (state.failed) return;
							if ( state.backtracking==0 ) { conditions.add(Pair.create(key, ColumnCondition.Raw.collectionCondition(t, element, op))); }
							}
							break;
						case 2 :
							// Parser.g:1603:15: K_IN (values= singleColumnInValues |marker= inMarker )
							{
							match(input,K_IN,FOLLOW_K_IN_in_columnCondition11767); if (state.failed) return;
							// Parser.g:1604:17: (values= singleColumnInValues |marker= inMarker )
							int alt207=2;
							int LA207_0 = input.LA(1);
							if ( (LA207_0==190) ) {
								alt207=1;
							}
							else if ( (LA207_0==QMARK||LA207_0==199) ) {
								alt207=2;
							}

							else {
								if (state.backtracking>0) {state.failed=true; return;}
								NoViableAltException nvae =
									new NoViableAltException("", 207, 0, input);
								throw nvae;
							}

							switch (alt207) {
								case 1 :
									// Parser.g:1604:19: values= singleColumnInValues
									{
									pushFollow(FOLLOW_singleColumnInValues_in_columnCondition11789);
									values=singleColumnInValues();
									state._fsp--;
									if (state.failed) return;
									if ( state.backtracking==0 ) { conditions.add(Pair.create(key, ColumnCondition.Raw.collectionInCondition(element, values))); }
									}
									break;
								case 2 :
									// Parser.g:1605:19: marker= inMarker
									{
									pushFollow(FOLLOW_inMarker_in_columnCondition11813);
									marker=inMarker();
									state._fsp--;
									if (state.failed) return;
									if ( state.backtracking==0 ) { conditions.add(Pair.create(key, ColumnCondition.Raw.collectionInCondition(element, marker))); }
									}
									break;

							}

							}
							break;

					}

					}
					break;
				case 4 :
					// Parser.g:1608:11: '.' field= fident (op= relationType t= term | K_IN (values= singleColumnInValues |marker= inMarker ) )
					{
					match(input,197,FOLLOW_197_in_columnCondition11859); if (state.failed) return;
					pushFollow(FOLLOW_fident_in_columnCondition11863);
					field=fident();
					state._fsp--;
					if (state.failed) return;
					// Parser.g:1609:13: (op= relationType t= term | K_IN (values= singleColumnInValues |marker= inMarker ) )
					int alt210=2;
					int LA210_0 = input.LA(1);
					if ( (LA210_0==188||(LA210_0 >= 201 && LA210_0 <= 205)) ) {
						alt210=1;
					}
					else if ( (LA210_0==K_IN) ) {
						alt210=2;
					}

					else {
						if (state.backtracking>0) {state.failed=true; return;}
						NoViableAltException nvae =
							new NoViableAltException("", 210, 0, input);
						throw nvae;
					}

					switch (alt210) {
						case 1 :
							// Parser.g:1609:15: op= relationType t= term
							{
							pushFollow(FOLLOW_relationType_in_columnCondition11881);
							op=relationType();
							state._fsp--;
							if (state.failed) return;
							pushFollow(FOLLOW_term_in_columnCondition11885);
							t=term();
							state._fsp--;
							if (state.failed) return;
							if ( state.backtracking==0 ) { conditions.add(Pair.create(key, ColumnCondition.Raw.udtFieldCondition(t, field, op))); }
							}
							break;
						case 2 :
							// Parser.g:1610:15: K_IN (values= singleColumnInValues |marker= inMarker )
							{
							match(input,K_IN,FOLLOW_K_IN_in_columnCondition11903); if (state.failed) return;
							// Parser.g:1611:17: (values= singleColumnInValues |marker= inMarker )
							int alt209=2;
							int LA209_0 = input.LA(1);
							if ( (LA209_0==190) ) {
								alt209=1;
							}
							else if ( (LA209_0==QMARK||LA209_0==199) ) {
								alt209=2;
							}

							else {
								if (state.backtracking>0) {state.failed=true; return;}
								NoViableAltException nvae =
									new NoViableAltException("", 209, 0, input);
								throw nvae;
							}

							switch (alt209) {
								case 1 :
									// Parser.g:1611:19: values= singleColumnInValues
									{
									pushFollow(FOLLOW_singleColumnInValues_in_columnCondition11925);
									values=singleColumnInValues();
									state._fsp--;
									if (state.failed) return;
									if ( state.backtracking==0 ) { conditions.add(Pair.create(key, ColumnCondition.Raw.udtFieldInCondition(field, values))); }
									}
									break;
								case 2 :
									// Parser.g:1612:19: marker= inMarker
									{
									pushFollow(FOLLOW_inMarker_in_columnCondition11949);
									marker=inMarker();
									state._fsp--;
									if (state.failed) return;
									if ( state.backtracking==0 ) { conditions.add(Pair.create(key, ColumnCondition.Raw.udtFieldInCondition(field, marker))); }
									}
									break;

							}

							}
							break;

					}

					}
					break;

			}

			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "columnCondition"



	// $ANTLR start "properties"
	// Parser.g:1618:1: properties[PropertyDefinitions props] : property[props] ( K_AND property[props] )* ;
	public final void properties(PropertyDefinitions props) throws RecognitionException {
		try {
			// Parser.g:1619:5: ( property[props] ( K_AND property[props] )* )
			// Parser.g:1619:7: property[props] ( K_AND property[props] )*
			{
			pushFollow(FOLLOW_property_in_properties12011);
			property(props);
			state._fsp--;
			if (state.failed) return;
			// Parser.g:1619:23: ( K_AND property[props] )*
			loop212:
			while (true) {
				int alt212=2;
				int LA212_0 = input.LA(1);
				if ( (LA212_0==K_AND) ) {
					alt212=1;
				}

				switch (alt212) {
				case 1 :
					// Parser.g:1619:24: K_AND property[props]
					{
					match(input,K_AND,FOLLOW_K_AND_in_properties12015); if (state.failed) return;
					pushFollow(FOLLOW_property_in_properties12017);
					property(props);
					state._fsp--;
					if (state.failed) return;
					}
					break;

				default :
					break loop212;
				}
			}

			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "properties"



	// $ANTLR start "property"
	// Parser.g:1622:1: property[PropertyDefinitions props] : (k= noncol_ident '=' simple= propertyValue |k= noncol_ident '=' map= fullMapLiteral );
	public final void property(PropertyDefinitions props) throws RecognitionException {
		ColumnIdentifier k =null;
		String simple =null;
		Maps.Literal map =null;

		try {
			// Parser.g:1623:5: (k= noncol_ident '=' simple= propertyValue |k= noncol_ident '=' map= fullMapLiteral )
			int alt213=2;
			alt213 = dfa213.predict(input);
			switch (alt213) {
				case 1 :
					// Parser.g:1623:7: k= noncol_ident '=' simple= propertyValue
					{
					pushFollow(FOLLOW_noncol_ident_in_property12040);
					k=noncol_ident();
					state._fsp--;
					if (state.failed) return;
					match(input,203,FOLLOW_203_in_property12042); if (state.failed) return;
					pushFollow(FOLLOW_propertyValue_in_property12046);
					simple=propertyValue();
					state._fsp--;
					if (state.failed) return;
					if ( state.backtracking==0 ) { try { props.addProperty(k.toString(), simple); } catch (SyntaxException e) { addRecognitionError(e.getMessage()); } }
					}
					break;
				case 2 :
					// Parser.g:1624:7: k= noncol_ident '=' map= fullMapLiteral
					{
					pushFollow(FOLLOW_noncol_ident_in_property12058);
					k=noncol_ident();
					state._fsp--;
					if (state.failed) return;
					match(input,203,FOLLOW_203_in_property12060); if (state.failed) return;
					pushFollow(FOLLOW_fullMapLiteral_in_property12064);
					map=fullMapLiteral();
					state._fsp--;
					if (state.failed) return;
					if ( state.backtracking==0 ) { try { props.addProperty(k.toString(), convertPropertyMap(map)); } catch (SyntaxException e) { addRecognitionError(e.getMessage()); } }
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "property"



	// $ANTLR start "propertyValue"
	// Parser.g:1627:1: propertyValue returns [String str] : (c= constant |u= unreserved_keyword );
	public final String propertyValue() throws RecognitionException {
		String str = null;


		Constants.Literal c =null;
		String u =null;

		try {
			// Parser.g:1628:5: (c= constant |u= unreserved_keyword )
			int alt214=2;
			int LA214_0 = input.LA(1);
			if ( (LA214_0==BOOLEAN||LA214_0==DURATION||LA214_0==FLOAT||LA214_0==HEXNUMBER||LA214_0==INTEGER||(LA214_0 >= K_NEGATIVE_INFINITY && LA214_0 <= K_NEGATIVE_NAN)||(LA214_0 >= K_POSITIVE_INFINITY && LA214_0 <= K_POSITIVE_NAN)||LA214_0==STRING_LITERAL||LA214_0==UUID) ) {
				alt214=1;
			}
			else if ( ((LA214_0 >= K_AGGREGATE && LA214_0 <= K_ALL)||LA214_0==K_AS||LA214_0==K_ASCII||(LA214_0 >= K_BIGINT && LA214_0 <= K_BOOLEAN)||(LA214_0 >= K_CALLED && LA214_0 <= K_CLUSTERING)||(LA214_0 >= K_COMPACT && LA214_0 <= K_COUNTER)||LA214_0==K_CUSTOM||(LA214_0 >= K_DATE && LA214_0 <= K_DECIMAL)||(LA214_0 >= K_DISTINCT && LA214_0 <= K_DOUBLE)||LA214_0==K_DURATION||(LA214_0 >= K_EXISTS && LA214_0 <= K_FLOAT)||LA214_0==K_FROZEN||(LA214_0 >= K_FUNCTION && LA214_0 <= K_FUNCTIONS)||LA214_0==K_GROUP||(LA214_0 >= K_INET && LA214_0 <= K_INPUT)||LA214_0==K_INT||(LA214_0 >= K_JSON && LA214_0 <= K_KEYS)||(LA214_0 >= K_KEYSPACES && LA214_0 <= K_LIKE)||(LA214_0 >= K_LIST && LA214_0 <= K_MAP)||LA214_0==K_NOLOGIN||LA214_0==K_NOSUPERUSER||LA214_0==K_OPTIONS||(LA214_0 >= K_PARTITION && LA214_0 <= K_PERMISSIONS)||LA214_0==K_RETURNS||(LA214_0 >= K_ROLE && LA214_0 <= K_ROLES)||(LA214_0 >= K_SFUNC && LA214_0 <= K_TINYINT)||LA214_0==K_TRIGGER||(LA214_0 >= K_TTL && LA214_0 <= K_TYPE)||(LA214_0 >= K_USER && LA214_0 <= K_USERS)||(LA214_0 >= K_UUID && LA214_0 <= K_VARINT)||LA214_0==K_WRITETIME) ) {
				alt214=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return str;}
				NoViableAltException nvae =
					new NoViableAltException("", 214, 0, input);
				throw nvae;
			}

			switch (alt214) {
				case 1 :
					// Parser.g:1628:7: c= constant
					{
					pushFollow(FOLLOW_constant_in_propertyValue12089);
					c=constant();
					state._fsp--;
					if (state.failed) return str;
					if ( state.backtracking==0 ) { str = c.getRawText(); }
					}
					break;
				case 2 :
					// Parser.g:1629:7: u= unreserved_keyword
					{
					pushFollow(FOLLOW_unreserved_keyword_in_propertyValue12111);
					u=unreserved_keyword();
					state._fsp--;
					if (state.failed) return str;
					if ( state.backtracking==0 ) { str = u; }
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return str;
	}
	// $ANTLR end "propertyValue"



	// $ANTLR start "relationType"
	// Parser.g:1632:1: relationType returns [Operator op] : ( '=' | '<' | '<=' | '>' | '>=' | '!=' );
	public final Operator relationType() throws RecognitionException {
		Operator op = null;


		try {
			// Parser.g:1633:5: ( '=' | '<' | '<=' | '>' | '>=' | '!=' )
			int alt215=6;
			switch ( input.LA(1) ) {
			case 203:
				{
				alt215=1;
				}
				break;
			case 201:
				{
				alt215=2;
				}
				break;
			case 202:
				{
				alt215=3;
				}
				break;
			case 204:
				{
				alt215=4;
				}
				break;
			case 205:
				{
				alt215=5;
				}
				break;
			case 188:
				{
				alt215=6;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return op;}
				NoViableAltException nvae =
					new NoViableAltException("", 215, 0, input);
				throw nvae;
			}
			switch (alt215) {
				case 1 :
					// Parser.g:1633:7: '='
					{
					match(input,203,FOLLOW_203_in_relationType12134); if (state.failed) return op;
					if ( state.backtracking==0 ) { op = Operator.EQ; }
					}
					break;
				case 2 :
					// Parser.g:1634:7: '<'
					{
					match(input,201,FOLLOW_201_in_relationType12145); if (state.failed) return op;
					if ( state.backtracking==0 ) { op = Operator.LT; }
					}
					break;
				case 3 :
					// Parser.g:1635:7: '<='
					{
					match(input,202,FOLLOW_202_in_relationType12156); if (state.failed) return op;
					if ( state.backtracking==0 ) { op = Operator.LTE; }
					}
					break;
				case 4 :
					// Parser.g:1636:7: '>'
					{
					match(input,204,FOLLOW_204_in_relationType12166); if (state.failed) return op;
					if ( state.backtracking==0 ) { op = Operator.GT; }
					}
					break;
				case 5 :
					// Parser.g:1637:7: '>='
					{
					match(input,205,FOLLOW_205_in_relationType12177); if (state.failed) return op;
					if ( state.backtracking==0 ) { op = Operator.GTE; }
					}
					break;
				case 6 :
					// Parser.g:1638:7: '!='
					{
					match(input,188,FOLLOW_188_in_relationType12187); if (state.failed) return op;
					if ( state.backtracking==0 ) { op = Operator.NEQ; }
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return op;
	}
	// $ANTLR end "relationType"



	// $ANTLR start "relation"
	// Parser.g:1641:1: relation[WhereClause.Builder clauses] : (name= cident type= relationType t= term |name= cident K_LIKE t= term |name= cident K_IS K_NOT K_NULL | K_TOKEN l= tupleOfIdentifiers type= relationType t= term |name= cident K_IN marker= inMarker |name= cident K_IN inValues= singleColumnInValues |name= cident rt= containsOperator t= term |name= cident '[' key= term ']' type= relationType t= term |ids= tupleOfIdentifiers ( K_IN ( '(' ')' |tupleInMarker= inMarkerForTuple |literals= tupleOfTupleLiterals |markers= tupleOfMarkersForTuples ) |type= relationType literal= tupleLiteral |type= relationType tupleMarker= markerForTuple ) | '(' relation[$clauses] ')' );
	public final void relation(WhereClause.Builder clauses) throws RecognitionException {
		ColumnMetadata.Raw name =null;
		Operator type =null;
		Term.Raw t =null;
		List<ColumnMetadata.Raw> l =null;
		AbstractMarker.INRaw marker =null;
		List<Term.Raw> inValues =null;
		Operator rt =null;
		Term.Raw key =null;
		List<ColumnMetadata.Raw> ids =null;
		Tuples.INRaw tupleInMarker =null;
		List<Tuples.Literal> literals =null;
		List<Tuples.Raw> markers =null;
		Tuples.Literal literal =null;
		Tuples.Raw tupleMarker =null;

		try {
			// Parser.g:1642:5: (name= cident type= relationType t= term |name= cident K_LIKE t= term |name= cident K_IS K_NOT K_NULL | K_TOKEN l= tupleOfIdentifiers type= relationType t= term |name= cident K_IN marker= inMarker |name= cident K_IN inValues= singleColumnInValues |name= cident rt= containsOperator t= term |name= cident '[' key= term ']' type= relationType t= term |ids= tupleOfIdentifiers ( K_IN ( '(' ')' |tupleInMarker= inMarkerForTuple |literals= tupleOfTupleLiterals |markers= tupleOfMarkersForTuples ) |type= relationType literal= tupleLiteral |type= relationType tupleMarker= markerForTuple ) | '(' relation[$clauses] ')' )
			int alt218=10;
			alt218 = dfa218.predict(input);
			switch (alt218) {
				case 1 :
					// Parser.g:1642:7: name= cident type= relationType t= term
					{
					pushFollow(FOLLOW_cident_in_relation12209);
					name=cident();
					state._fsp--;
					if (state.failed) return;
					pushFollow(FOLLOW_relationType_in_relation12213);
					type=relationType();
					state._fsp--;
					if (state.failed) return;
					pushFollow(FOLLOW_term_in_relation12217);
					t=term();
					state._fsp--;
					if (state.failed) return;
					if ( state.backtracking==0 ) { clauses.add(new SingleColumnRelation(name, type, t)); }
					}
					break;
				case 2 :
					// Parser.g:1643:7: name= cident K_LIKE t= term
					{
					pushFollow(FOLLOW_cident_in_relation12229);
					name=cident();
					state._fsp--;
					if (state.failed) return;
					match(input,K_LIKE,FOLLOW_K_LIKE_in_relation12231); if (state.failed) return;
					pushFollow(FOLLOW_term_in_relation12235);
					t=term();
					state._fsp--;
					if (state.failed) return;
					if ( state.backtracking==0 ) { clauses.add(new SingleColumnRelation(name, Operator.LIKE, t)); }
					}
					break;
				case 3 :
					// Parser.g:1644:7: name= cident K_IS K_NOT K_NULL
					{
					pushFollow(FOLLOW_cident_in_relation12247);
					name=cident();
					state._fsp--;
					if (state.failed) return;
					match(input,K_IS,FOLLOW_K_IS_in_relation12249); if (state.failed) return;
					match(input,K_NOT,FOLLOW_K_NOT_in_relation12251); if (state.failed) return;
					match(input,K_NULL,FOLLOW_K_NULL_in_relation12253); if (state.failed) return;
					if ( state.backtracking==0 ) { clauses.add(new SingleColumnRelation(name, Operator.IS_NOT, Constants.NULL_LITERAL)); }
					}
					break;
				case 4 :
					// Parser.g:1645:7: K_TOKEN l= tupleOfIdentifiers type= relationType t= term
					{
					match(input,K_TOKEN,FOLLOW_K_TOKEN_in_relation12263); if (state.failed) return;
					pushFollow(FOLLOW_tupleOfIdentifiers_in_relation12267);
					l=tupleOfIdentifiers();
					state._fsp--;
					if (state.failed) return;
					pushFollow(FOLLOW_relationType_in_relation12271);
					type=relationType();
					state._fsp--;
					if (state.failed) return;
					pushFollow(FOLLOW_term_in_relation12275);
					t=term();
					state._fsp--;
					if (state.failed) return;
					if ( state.backtracking==0 ) { clauses.add(new TokenRelation(l, type, t)); }
					}
					break;
				case 5 :
					// Parser.g:1647:7: name= cident K_IN marker= inMarker
					{
					pushFollow(FOLLOW_cident_in_relation12295);
					name=cident();
					state._fsp--;
					if (state.failed) return;
					match(input,K_IN,FOLLOW_K_IN_in_relation12297); if (state.failed) return;
					pushFollow(FOLLOW_inMarker_in_relation12301);
					marker=inMarker();
					state._fsp--;
					if (state.failed) return;
					if ( state.backtracking==0 ) { clauses.add(new SingleColumnRelation(name, Operator.IN, marker)); }
					}
					break;
				case 6 :
					// Parser.g:1649:7: name= cident K_IN inValues= singleColumnInValues
					{
					pushFollow(FOLLOW_cident_in_relation12321);
					name=cident();
					state._fsp--;
					if (state.failed) return;
					match(input,K_IN,FOLLOW_K_IN_in_relation12323); if (state.failed) return;
					pushFollow(FOLLOW_singleColumnInValues_in_relation12327);
					inValues=singleColumnInValues();
					state._fsp--;
					if (state.failed) return;
					if ( state.backtracking==0 ) { clauses.add(SingleColumnRelation.createInRelation(name, inValues)); }
					}
					break;
				case 7 :
					// Parser.g:1651:7: name= cident rt= containsOperator t= term
					{
					pushFollow(FOLLOW_cident_in_relation12347);
					name=cident();
					state._fsp--;
					if (state.failed) return;
					pushFollow(FOLLOW_containsOperator_in_relation12351);
					rt=containsOperator();
					state._fsp--;
					if (state.failed) return;
					pushFollow(FOLLOW_term_in_relation12355);
					t=term();
					state._fsp--;
					if (state.failed) return;
					if ( state.backtracking==0 ) { clauses.add(new SingleColumnRelation(name, rt, t)); }
					}
					break;
				case 8 :
					// Parser.g:1652:7: name= cident '[' key= term ']' type= relationType t= term
					{
					pushFollow(FOLLOW_cident_in_relation12367);
					name=cident();
					state._fsp--;
					if (state.failed) return;
					match(input,206,FOLLOW_206_in_relation12369); if (state.failed) return;
					pushFollow(FOLLOW_term_in_relation12373);
					key=term();
					state._fsp--;
					if (state.failed) return;
					match(input,208,FOLLOW_208_in_relation12375); if (state.failed) return;
					pushFollow(FOLLOW_relationType_in_relation12379);
					type=relationType();
					state._fsp--;
					if (state.failed) return;
					pushFollow(FOLLOW_term_in_relation12383);
					t=term();
					state._fsp--;
					if (state.failed) return;
					if ( state.backtracking==0 ) { clauses.add(new SingleColumnRelation(name, key, type, t)); }
					}
					break;
				case 9 :
					// Parser.g:1653:7: ids= tupleOfIdentifiers ( K_IN ( '(' ')' |tupleInMarker= inMarkerForTuple |literals= tupleOfTupleLiterals |markers= tupleOfMarkersForTuples ) |type= relationType literal= tupleLiteral |type= relationType tupleMarker= markerForTuple )
					{
					pushFollow(FOLLOW_tupleOfIdentifiers_in_relation12395);
					ids=tupleOfIdentifiers();
					state._fsp--;
					if (state.failed) return;
					// Parser.g:1654:7: ( K_IN ( '(' ')' |tupleInMarker= inMarkerForTuple |literals= tupleOfTupleLiterals |markers= tupleOfMarkersForTuples ) |type= relationType literal= tupleLiteral |type= relationType tupleMarker= markerForTuple )
					int alt217=3;
					alt217 = dfa217.predict(input);
					switch (alt217) {
						case 1 :
							// Parser.g:1654:9: K_IN ( '(' ')' |tupleInMarker= inMarkerForTuple |literals= tupleOfTupleLiterals |markers= tupleOfMarkersForTuples )
							{
							match(input,K_IN,FOLLOW_K_IN_in_relation12405); if (state.failed) return;
							// Parser.g:1655:11: ( '(' ')' |tupleInMarker= inMarkerForTuple |literals= tupleOfTupleLiterals |markers= tupleOfMarkersForTuples )
							int alt216=4;
							int LA216_0 = input.LA(1);
							if ( (LA216_0==190) ) {
								switch ( input.LA(2) ) {
								case 191:
									{
									alt216=1;
									}
									break;
								case 190:
									{
									alt216=3;
									}
									break;
								case QMARK:
								case 199:
									{
									alt216=4;
									}
									break;
								default:
									if (state.backtracking>0) {state.failed=true; return;}
									int nvaeMark = input.mark();
									try {
										input.consume();
										NoViableAltException nvae =
											new NoViableAltException("", 216, 1, input);
										throw nvae;
									} finally {
										input.rewind(nvaeMark);
									}
								}
							}
							else if ( (LA216_0==QMARK||LA216_0==199) ) {
								alt216=2;
							}

							else {
								if (state.backtracking>0) {state.failed=true; return;}
								NoViableAltException nvae =
									new NoViableAltException("", 216, 0, input);
								throw nvae;
							}

							switch (alt216) {
								case 1 :
									// Parser.g:1655:13: '(' ')'
									{
									match(input,190,FOLLOW_190_in_relation12419); if (state.failed) return;
									match(input,191,FOLLOW_191_in_relation12421); if (state.failed) return;
									if ( state.backtracking==0 ) { clauses.add(MultiColumnRelation.createInRelation(ids, new ArrayList<Tuples.Literal>())); }
									}
									break;
								case 2 :
									// Parser.g:1657:13: tupleInMarker= inMarkerForTuple
									{
									pushFollow(FOLLOW_inMarkerForTuple_in_relation12453);
									tupleInMarker=inMarkerForTuple();
									state._fsp--;
									if (state.failed) return;
									if ( state.backtracking==0 ) { clauses.add(MultiColumnRelation.createSingleMarkerInRelation(ids, tupleInMarker)); }
									}
									break;
								case 3 :
									// Parser.g:1659:13: literals= tupleOfTupleLiterals
									{
									pushFollow(FOLLOW_tupleOfTupleLiterals_in_relation12487);
									literals=tupleOfTupleLiterals();
									state._fsp--;
									if (state.failed) return;
									if ( state.backtracking==0 ) {
									                  clauses.add(MultiColumnRelation.createInRelation(ids, literals));
									              }
									}
									break;
								case 4 :
									// Parser.g:1663:13: markers= tupleOfMarkersForTuples
									{
									pushFollow(FOLLOW_tupleOfMarkersForTuples_in_relation12521);
									markers=tupleOfMarkersForTuples();
									state._fsp--;
									if (state.failed) return;
									if ( state.backtracking==0 ) { clauses.add(MultiColumnRelation.createInRelation(ids, markers)); }
									}
									break;

							}

							}
							break;
						case 2 :
							// Parser.g:1666:9: type= relationType literal= tupleLiteral
							{
							pushFollow(FOLLOW_relationType_in_relation12563);
							type=relationType();
							state._fsp--;
							if (state.failed) return;
							pushFollow(FOLLOW_tupleLiteral_in_relation12567);
							literal=tupleLiteral();
							state._fsp--;
							if (state.failed) return;
							if ( state.backtracking==0 ) {
							              clauses.add(MultiColumnRelation.createNonInRelation(ids, type, literal));
							          }
							}
							break;
						case 3 :
							// Parser.g:1670:9: type= relationType tupleMarker= markerForTuple
							{
							pushFollow(FOLLOW_relationType_in_relation12593);
							type=relationType();
							state._fsp--;
							if (state.failed) return;
							pushFollow(FOLLOW_markerForTuple_in_relation12597);
							tupleMarker=markerForTuple();
							state._fsp--;
							if (state.failed) return;
							if ( state.backtracking==0 ) { clauses.add(MultiColumnRelation.createNonInRelation(ids, type, tupleMarker)); }
							}
							break;

					}

					}
					break;
				case 10 :
					// Parser.g:1673:7: '(' relation[$clauses] ')'
					{
					match(input,190,FOLLOW_190_in_relation12627); if (state.failed) return;
					pushFollow(FOLLOW_relation_in_relation12629);
					relation(clauses);
					state._fsp--;
					if (state.failed) return;
					match(input,191,FOLLOW_191_in_relation12632); if (state.failed) return;
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "relation"



	// $ANTLR start "containsOperator"
	// Parser.g:1676:1: containsOperator returns [Operator o] : K_CONTAINS ( K_KEY )? ;
	public final Operator containsOperator() throws RecognitionException {
		Operator o = null;


		try {
			// Parser.g:1677:5: ( K_CONTAINS ( K_KEY )? )
			// Parser.g:1677:7: K_CONTAINS ( K_KEY )?
			{
			match(input,K_CONTAINS,FOLLOW_K_CONTAINS_in_containsOperator12653); if (state.failed) return o;
			if ( state.backtracking==0 ) { o = Operator.CONTAINS; }
			// Parser.g:1677:45: ( K_KEY )?
			int alt219=2;
			int LA219_0 = input.LA(1);
			if ( (LA219_0==K_KEY) ) {
				int LA219_1 = input.LA(2);
				if ( (LA219_1==BOOLEAN||LA219_1==DURATION||LA219_1==FLOAT||LA219_1==HEXNUMBER||(LA219_1 >= IDENT && LA219_1 <= INTEGER)||(LA219_1 >= K_AGGREGATE && LA219_1 <= K_ALL)||LA219_1==K_AS||LA219_1==K_ASCII||(LA219_1 >= K_BIGINT && LA219_1 <= K_BOOLEAN)||(LA219_1 >= K_CALLED && LA219_1 <= K_CLUSTERING)||(LA219_1 >= K_COMPACT && LA219_1 <= K_COUNTER)||LA219_1==K_CUSTOM||(LA219_1 >= K_DATE && LA219_1 <= K_DECIMAL)||(LA219_1 >= K_DISTINCT && LA219_1 <= K_DOUBLE)||LA219_1==K_DURATION||(LA219_1 >= K_EXISTS && LA219_1 <= K_FLOAT)||LA219_1==K_FROZEN||(LA219_1 >= K_FUNCTION && LA219_1 <= K_FUNCTIONS)||LA219_1==K_GROUP||(LA219_1 >= K_INET && LA219_1 <= K_INPUT)||LA219_1==K_INT||(LA219_1 >= K_JSON && LA219_1 <= K_KEYS)||(LA219_1 >= K_KEYSPACES && LA219_1 <= K_LIKE)||(LA219_1 >= K_LIST && LA219_1 <= K_MAP)||(LA219_1 >= K_NEGATIVE_INFINITY && LA219_1 <= K_NOLOGIN)||LA219_1==K_NOSUPERUSER||LA219_1==K_NULL||LA219_1==K_OPTIONS||(LA219_1 >= K_PARTITION && LA219_1 <= K_POSITIVE_NAN)||LA219_1==K_RETURNS||(LA219_1 >= K_ROLE && LA219_1 <= K_ROLES)||(LA219_1 >= K_SFUNC && LA219_1 <= K_TINYINT)||(LA219_1 >= K_TOKEN && LA219_1 <= K_TRIGGER)||(LA219_1 >= K_TTL && LA219_1 <= K_TYPE)||(LA219_1 >= K_USER && LA219_1 <= K_USERS)||(LA219_1 >= K_UUID && LA219_1 <= K_VARINT)||LA219_1==K_WRITETIME||(LA219_1 >= QMARK && LA219_1 <= QUOTED_NAME)||LA219_1==STRING_LITERAL||LA219_1==UUID||LA219_1==190||LA219_1==195||LA219_1==199||LA219_1==206||LA219_1==210) ) {
					alt219=1;
				}
			}
			switch (alt219) {
				case 1 :
					// Parser.g:1677:46: K_KEY
					{
					match(input,K_KEY,FOLLOW_K_KEY_in_containsOperator12658); if (state.failed) return o;
					if ( state.backtracking==0 ) { o = Operator.CONTAINS_KEY; }
					}
					break;

			}

			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return o;
	}
	// $ANTLR end "containsOperator"



	// $ANTLR start "inMarker"
	// Parser.g:1680:1: inMarker returns [AbstractMarker.INRaw marker] : ( QMARK | ':' name= noncol_ident );
	public final AbstractMarker.INRaw inMarker() throws RecognitionException {
		AbstractMarker.INRaw marker = null;


		ColumnIdentifier name =null;

		try {
			// Parser.g:1681:5: ( QMARK | ':' name= noncol_ident )
			int alt220=2;
			int LA220_0 = input.LA(1);
			if ( (LA220_0==QMARK) ) {
				alt220=1;
			}
			else if ( (LA220_0==199) ) {
				alt220=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return marker;}
				NoViableAltException nvae =
					new NoViableAltException("", 220, 0, input);
				throw nvae;
			}

			switch (alt220) {
				case 1 :
					// Parser.g:1681:7: QMARK
					{
					match(input,QMARK,FOLLOW_QMARK_in_inMarker12683); if (state.failed) return marker;
					if ( state.backtracking==0 ) { marker = newINBindVariables(null); }
					}
					break;
				case 2 :
					// Parser.g:1682:7: ':' name= noncol_ident
					{
					match(input,199,FOLLOW_199_in_inMarker12693); if (state.failed) return marker;
					pushFollow(FOLLOW_noncol_ident_in_inMarker12697);
					name=noncol_ident();
					state._fsp--;
					if (state.failed) return marker;
					if ( state.backtracking==0 ) { marker = newINBindVariables(name); }
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return marker;
	}
	// $ANTLR end "inMarker"



	// $ANTLR start "tupleOfIdentifiers"
	// Parser.g:1685:1: tupleOfIdentifiers returns [List<ColumnMetadata.Raw> ids] : '(' n1= cident ( ',' ni= cident )* ')' ;
	public final List<ColumnMetadata.Raw> tupleOfIdentifiers() throws RecognitionException {
		List<ColumnMetadata.Raw> ids = null;


		ColumnMetadata.Raw n1 =null;
		ColumnMetadata.Raw ni =null;

		 ids = new ArrayList<ColumnMetadata.Raw>(); 
		try {
			// Parser.g:1687:5: ( '(' n1= cident ( ',' ni= cident )* ')' )
			// Parser.g:1687:7: '(' n1= cident ( ',' ni= cident )* ')'
			{
			match(input,190,FOLLOW_190_in_tupleOfIdentifiers12729); if (state.failed) return ids;
			pushFollow(FOLLOW_cident_in_tupleOfIdentifiers12733);
			n1=cident();
			state._fsp--;
			if (state.failed) return ids;
			if ( state.backtracking==0 ) { ids.add(n1); }
			// Parser.g:1687:39: ( ',' ni= cident )*
			loop221:
			while (true) {
				int alt221=2;
				int LA221_0 = input.LA(1);
				if ( (LA221_0==194) ) {
					alt221=1;
				}

				switch (alt221) {
				case 1 :
					// Parser.g:1687:40: ',' ni= cident
					{
					match(input,194,FOLLOW_194_in_tupleOfIdentifiers12738); if (state.failed) return ids;
					pushFollow(FOLLOW_cident_in_tupleOfIdentifiers12742);
					ni=cident();
					state._fsp--;
					if (state.failed) return ids;
					if ( state.backtracking==0 ) { ids.add(ni); }
					}
					break;

				default :
					break loop221;
				}
			}

			match(input,191,FOLLOW_191_in_tupleOfIdentifiers12748); if (state.failed) return ids;
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return ids;
	}
	// $ANTLR end "tupleOfIdentifiers"



	// $ANTLR start "singleColumnInValues"
	// Parser.g:1690:1: singleColumnInValues returns [List<Term.Raw> terms] : '(' (t1= term ( ',' ti= term )* )? ')' ;
	public final List<Term.Raw> singleColumnInValues() throws RecognitionException {
		List<Term.Raw> terms = null;


		Term.Raw t1 =null;
		Term.Raw ti =null;

		 terms = new ArrayList<Term.Raw>(); 
		try {
			// Parser.g:1692:5: ( '(' (t1= term ( ',' ti= term )* )? ')' )
			// Parser.g:1692:7: '(' (t1= term ( ',' ti= term )* )? ')'
			{
			match(input,190,FOLLOW_190_in_singleColumnInValues12778); if (state.failed) return terms;
			// Parser.g:1692:11: (t1= term ( ',' ti= term )* )?
			int alt223=2;
			int LA223_0 = input.LA(1);
			if ( (LA223_0==BOOLEAN||LA223_0==DURATION||LA223_0==FLOAT||LA223_0==HEXNUMBER||(LA223_0 >= IDENT && LA223_0 <= INTEGER)||(LA223_0 >= K_AGGREGATE && LA223_0 <= K_ALL)||LA223_0==K_AS||LA223_0==K_ASCII||(LA223_0 >= K_BIGINT && LA223_0 <= K_BOOLEAN)||(LA223_0 >= K_CALLED && LA223_0 <= K_CLUSTERING)||(LA223_0 >= K_COMPACT && LA223_0 <= K_COUNTER)||LA223_0==K_CUSTOM||(LA223_0 >= K_DATE && LA223_0 <= K_DECIMAL)||(LA223_0 >= K_DISTINCT && LA223_0 <= K_DOUBLE)||LA223_0==K_DURATION||(LA223_0 >= K_EXISTS && LA223_0 <= K_FLOAT)||LA223_0==K_FROZEN||(LA223_0 >= K_FUNCTION && LA223_0 <= K_FUNCTIONS)||LA223_0==K_GROUP||(LA223_0 >= K_INET && LA223_0 <= K_INPUT)||LA223_0==K_INT||(LA223_0 >= K_JSON && LA223_0 <= K_KEYS)||(LA223_0 >= K_KEYSPACES && LA223_0 <= K_LIKE)||(LA223_0 >= K_LIST && LA223_0 <= K_MAP)||(LA223_0 >= K_NEGATIVE_INFINITY && LA223_0 <= K_NOLOGIN)||LA223_0==K_NOSUPERUSER||LA223_0==K_NULL||LA223_0==K_OPTIONS||(LA223_0 >= K_PARTITION && LA223_0 <= K_POSITIVE_NAN)||LA223_0==K_RETURNS||(LA223_0 >= K_ROLE && LA223_0 <= K_ROLES)||(LA223_0 >= K_SFUNC && LA223_0 <= K_TINYINT)||(LA223_0 >= K_TOKEN && LA223_0 <= K_TRIGGER)||(LA223_0 >= K_TTL && LA223_0 <= K_TYPE)||(LA223_0 >= K_USER && LA223_0 <= K_USERS)||(LA223_0 >= K_UUID && LA223_0 <= K_VARINT)||LA223_0==K_WRITETIME||(LA223_0 >= QMARK && LA223_0 <= QUOTED_NAME)||LA223_0==STRING_LITERAL||LA223_0==UUID||LA223_0==190||LA223_0==195||LA223_0==199||LA223_0==206||LA223_0==210) ) {
				alt223=1;
			}
			switch (alt223) {
				case 1 :
					// Parser.g:1692:13: t1= term ( ',' ti= term )*
					{
					pushFollow(FOLLOW_term_in_singleColumnInValues12786);
					t1=term();
					state._fsp--;
					if (state.failed) return terms;
					if ( state.backtracking==0 ) { terms.add(t1); }
					// Parser.g:1692:43: ( ',' ti= term )*
					loop222:
					while (true) {
						int alt222=2;
						int LA222_0 = input.LA(1);
						if ( (LA222_0==194) ) {
							alt222=1;
						}

						switch (alt222) {
						case 1 :
							// Parser.g:1692:44: ',' ti= term
							{
							match(input,194,FOLLOW_194_in_singleColumnInValues12791); if (state.failed) return terms;
							pushFollow(FOLLOW_term_in_singleColumnInValues12795);
							ti=term();
							state._fsp--;
							if (state.failed) return terms;
							if ( state.backtracking==0 ) { terms.add(ti); }
							}
							break;

						default :
							break loop222;
						}
					}

					}
					break;

			}

			match(input,191,FOLLOW_191_in_singleColumnInValues12804); if (state.failed) return terms;
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return terms;
	}
	// $ANTLR end "singleColumnInValues"



	// $ANTLR start "tupleOfTupleLiterals"
	// Parser.g:1695:1: tupleOfTupleLiterals returns [List<Tuples.Literal> literals] : '(' t1= tupleLiteral ( ',' ti= tupleLiteral )* ')' ;
	public final List<Tuples.Literal> tupleOfTupleLiterals() throws RecognitionException {
		List<Tuples.Literal> literals = null;


		Tuples.Literal t1 =null;
		Tuples.Literal ti =null;

		 literals = new ArrayList<>(); 
		try {
			// Parser.g:1697:5: ( '(' t1= tupleLiteral ( ',' ti= tupleLiteral )* ')' )
			// Parser.g:1697:7: '(' t1= tupleLiteral ( ',' ti= tupleLiteral )* ')'
			{
			match(input,190,FOLLOW_190_in_tupleOfTupleLiterals12834); if (state.failed) return literals;
			pushFollow(FOLLOW_tupleLiteral_in_tupleOfTupleLiterals12838);
			t1=tupleLiteral();
			state._fsp--;
			if (state.failed) return literals;
			if ( state.backtracking==0 ) { literals.add(t1); }
			// Parser.g:1697:50: ( ',' ti= tupleLiteral )*
			loop224:
			while (true) {
				int alt224=2;
				int LA224_0 = input.LA(1);
				if ( (LA224_0==194) ) {
					alt224=1;
				}

				switch (alt224) {
				case 1 :
					// Parser.g:1697:51: ',' ti= tupleLiteral
					{
					match(input,194,FOLLOW_194_in_tupleOfTupleLiterals12843); if (state.failed) return literals;
					pushFollow(FOLLOW_tupleLiteral_in_tupleOfTupleLiterals12847);
					ti=tupleLiteral();
					state._fsp--;
					if (state.failed) return literals;
					if ( state.backtracking==0 ) { literals.add(ti); }
					}
					break;

				default :
					break loop224;
				}
			}

			match(input,191,FOLLOW_191_in_tupleOfTupleLiterals12853); if (state.failed) return literals;
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return literals;
	}
	// $ANTLR end "tupleOfTupleLiterals"



	// $ANTLR start "markerForTuple"
	// Parser.g:1700:1: markerForTuple returns [Tuples.Raw marker] : ( QMARK | ':' name= noncol_ident );
	public final Tuples.Raw markerForTuple() throws RecognitionException {
		Tuples.Raw marker = null;


		ColumnIdentifier name =null;

		try {
			// Parser.g:1701:5: ( QMARK | ':' name= noncol_ident )
			int alt225=2;
			int LA225_0 = input.LA(1);
			if ( (LA225_0==QMARK) ) {
				alt225=1;
			}
			else if ( (LA225_0==199) ) {
				alt225=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return marker;}
				NoViableAltException nvae =
					new NoViableAltException("", 225, 0, input);
				throw nvae;
			}

			switch (alt225) {
				case 1 :
					// Parser.g:1701:7: QMARK
					{
					match(input,QMARK,FOLLOW_QMARK_in_markerForTuple12874); if (state.failed) return marker;
					if ( state.backtracking==0 ) { marker = newTupleBindVariables(null); }
					}
					break;
				case 2 :
					// Parser.g:1702:7: ':' name= noncol_ident
					{
					match(input,199,FOLLOW_199_in_markerForTuple12884); if (state.failed) return marker;
					pushFollow(FOLLOW_noncol_ident_in_markerForTuple12888);
					name=noncol_ident();
					state._fsp--;
					if (state.failed) return marker;
					if ( state.backtracking==0 ) { marker = newTupleBindVariables(name); }
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return marker;
	}
	// $ANTLR end "markerForTuple"



	// $ANTLR start "tupleOfMarkersForTuples"
	// Parser.g:1705:1: tupleOfMarkersForTuples returns [List<Tuples.Raw> markers] : '(' m1= markerForTuple ( ',' mi= markerForTuple )* ')' ;
	public final List<Tuples.Raw> tupleOfMarkersForTuples() throws RecognitionException {
		List<Tuples.Raw> markers = null;


		Tuples.Raw m1 =null;
		Tuples.Raw mi =null;

		 markers = new ArrayList<Tuples.Raw>(); 
		try {
			// Parser.g:1707:5: ( '(' m1= markerForTuple ( ',' mi= markerForTuple )* ')' )
			// Parser.g:1707:7: '(' m1= markerForTuple ( ',' mi= markerForTuple )* ')'
			{
			match(input,190,FOLLOW_190_in_tupleOfMarkersForTuples12920); if (state.failed) return markers;
			pushFollow(FOLLOW_markerForTuple_in_tupleOfMarkersForTuples12924);
			m1=markerForTuple();
			state._fsp--;
			if (state.failed) return markers;
			if ( state.backtracking==0 ) { markers.add(m1); }
			// Parser.g:1707:51: ( ',' mi= markerForTuple )*
			loop226:
			while (true) {
				int alt226=2;
				int LA226_0 = input.LA(1);
				if ( (LA226_0==194) ) {
					alt226=1;
				}

				switch (alt226) {
				case 1 :
					// Parser.g:1707:52: ',' mi= markerForTuple
					{
					match(input,194,FOLLOW_194_in_tupleOfMarkersForTuples12929); if (state.failed) return markers;
					pushFollow(FOLLOW_markerForTuple_in_tupleOfMarkersForTuples12933);
					mi=markerForTuple();
					state._fsp--;
					if (state.failed) return markers;
					if ( state.backtracking==0 ) { markers.add(mi); }
					}
					break;

				default :
					break loop226;
				}
			}

			match(input,191,FOLLOW_191_in_tupleOfMarkersForTuples12939); if (state.failed) return markers;
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return markers;
	}
	// $ANTLR end "tupleOfMarkersForTuples"



	// $ANTLR start "inMarkerForTuple"
	// Parser.g:1710:1: inMarkerForTuple returns [Tuples.INRaw marker] : ( QMARK | ':' name= noncol_ident );
	public final Tuples.INRaw inMarkerForTuple() throws RecognitionException {
		Tuples.INRaw marker = null;


		ColumnIdentifier name =null;

		try {
			// Parser.g:1711:5: ( QMARK | ':' name= noncol_ident )
			int alt227=2;
			int LA227_0 = input.LA(1);
			if ( (LA227_0==QMARK) ) {
				alt227=1;
			}
			else if ( (LA227_0==199) ) {
				alt227=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return marker;}
				NoViableAltException nvae =
					new NoViableAltException("", 227, 0, input);
				throw nvae;
			}

			switch (alt227) {
				case 1 :
					// Parser.g:1711:7: QMARK
					{
					match(input,QMARK,FOLLOW_QMARK_in_inMarkerForTuple12960); if (state.failed) return marker;
					if ( state.backtracking==0 ) { marker = newTupleINBindVariables(null); }
					}
					break;
				case 2 :
					// Parser.g:1712:7: ':' name= noncol_ident
					{
					match(input,199,FOLLOW_199_in_inMarkerForTuple12970); if (state.failed) return marker;
					pushFollow(FOLLOW_noncol_ident_in_inMarkerForTuple12974);
					name=noncol_ident();
					state._fsp--;
					if (state.failed) return marker;
					if ( state.backtracking==0 ) { marker = newTupleINBindVariables(name); }
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return marker;
	}
	// $ANTLR end "inMarkerForTuple"



	// $ANTLR start "comparatorType"
	// Parser.g:1715:1: comparatorType returns [CQL3Type.Raw t] : (n= native_type |c= collection_type |tt= tuple_type |id= userTypeName | K_FROZEN '<' f= comparatorType '>' |s= STRING_LITERAL );
	public final CQL3Type.Raw comparatorType() throws RecognitionException {
		CQL3Type.Raw t = null;


		Token s=null;
		CQL3Type n =null;
		CQL3Type.Raw c =null;
		CQL3Type.Raw tt =null;
		UTName id =null;
		CQL3Type.Raw f =null;

		try {
			// Parser.g:1716:5: (n= native_type |c= collection_type |tt= tuple_type |id= userTypeName | K_FROZEN '<' f= comparatorType '>' |s= STRING_LITERAL )
			int alt228=6;
			alt228 = dfa228.predict(input);
			switch (alt228) {
				case 1 :
					// Parser.g:1716:7: n= native_type
					{
					pushFollow(FOLLOW_native_type_in_comparatorType12999);
					n=native_type();
					state._fsp--;
					if (state.failed) return t;
					if ( state.backtracking==0 ) { t = CQL3Type.Raw.from(n); }
					}
					break;
				case 2 :
					// Parser.g:1717:7: c= collection_type
					{
					pushFollow(FOLLOW_collection_type_in_comparatorType13015);
					c=collection_type();
					state._fsp--;
					if (state.failed) return t;
					if ( state.backtracking==0 ) { t = c; }
					}
					break;
				case 3 :
					// Parser.g:1718:7: tt= tuple_type
					{
					pushFollow(FOLLOW_tuple_type_in_comparatorType13027);
					tt=tuple_type();
					state._fsp--;
					if (state.failed) return t;
					if ( state.backtracking==0 ) { t = tt; }
					}
					break;
				case 4 :
					// Parser.g:1719:7: id= userTypeName
					{
					pushFollow(FOLLOW_userTypeName_in_comparatorType13043);
					id=userTypeName();
					state._fsp--;
					if (state.failed) return t;
					if ( state.backtracking==0 ) { t = CQL3Type.Raw.userType(id); }
					}
					break;
				case 5 :
					// Parser.g:1720:7: K_FROZEN '<' f= comparatorType '>'
					{
					match(input,K_FROZEN,FOLLOW_K_FROZEN_in_comparatorType13055); if (state.failed) return t;
					match(input,201,FOLLOW_201_in_comparatorType13057); if (state.failed) return t;
					pushFollow(FOLLOW_comparatorType_in_comparatorType13061);
					f=comparatorType();
					state._fsp--;
					if (state.failed) return t;
					match(input,204,FOLLOW_204_in_comparatorType13063); if (state.failed) return t;
					if ( state.backtracking==0 ) {
					        try {
					            t = f.freeze();
					        } catch (InvalidRequestException e) {
					            addRecognitionError(e.getMessage());
					        }
					      }
					}
					break;
				case 6 :
					// Parser.g:1728:7: s= STRING_LITERAL
					{
					s=(Token)match(input,STRING_LITERAL,FOLLOW_STRING_LITERAL_in_comparatorType13081); if (state.failed) return t;
					if ( state.backtracking==0 ) {
					        try {
					            t = CQL3Type.Raw.from(new CQL3Type.Custom((s!=null?s.getText():null)));
					        } catch (SyntaxException e) {
					            addRecognitionError("Cannot parse type " + (s!=null?s.getText():null) + ": " + e.getMessage());
					        } catch (ConfigurationException e) {
					            addRecognitionError("Error setting type " + (s!=null?s.getText():null) + ": " + e.getMessage());
					        }
					      }
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return t;
	}
	// $ANTLR end "comparatorType"



	// $ANTLR start "native_type"
	// Parser.g:1740:1: native_type returns [CQL3Type t] : ( K_ASCII | K_BIGINT | K_BLOB | K_BOOLEAN | K_COUNTER | K_DECIMAL | K_DOUBLE | K_DURATION | K_FLOAT | K_INET | K_INT | K_SMALLINT | K_TEXT | K_TIMESTAMP | K_TINYINT | K_UUID | K_VARCHAR | K_VARINT | K_TIMEUUID | K_DATE | K_TIME );
	public final CQL3Type native_type() throws RecognitionException {
		CQL3Type t = null;


		try {
			// Parser.g:1741:5: ( K_ASCII | K_BIGINT | K_BLOB | K_BOOLEAN | K_COUNTER | K_DECIMAL | K_DOUBLE | K_DURATION | K_FLOAT | K_INET | K_INT | K_SMALLINT | K_TEXT | K_TIMESTAMP | K_TINYINT | K_UUID | K_VARCHAR | K_VARINT | K_TIMEUUID | K_DATE | K_TIME )
			int alt229=21;
			switch ( input.LA(1) ) {
			case K_ASCII:
				{
				alt229=1;
				}
				break;
			case K_BIGINT:
				{
				alt229=2;
				}
				break;
			case K_BLOB:
				{
				alt229=3;
				}
				break;
			case K_BOOLEAN:
				{
				alt229=4;
				}
				break;
			case K_COUNTER:
				{
				alt229=5;
				}
				break;
			case K_DECIMAL:
				{
				alt229=6;
				}
				break;
			case K_DOUBLE:
				{
				alt229=7;
				}
				break;
			case K_DURATION:
				{
				alt229=8;
				}
				break;
			case K_FLOAT:
				{
				alt229=9;
				}
				break;
			case K_INET:
				{
				alt229=10;
				}
				break;
			case K_INT:
				{
				alt229=11;
				}
				break;
			case K_SMALLINT:
				{
				alt229=12;
				}
				break;
			case K_TEXT:
				{
				alt229=13;
				}
				break;
			case K_TIMESTAMP:
				{
				alt229=14;
				}
				break;
			case K_TINYINT:
				{
				alt229=15;
				}
				break;
			case K_UUID:
				{
				alt229=16;
				}
				break;
			case K_VARCHAR:
				{
				alt229=17;
				}
				break;
			case K_VARINT:
				{
				alt229=18;
				}
				break;
			case K_TIMEUUID:
				{
				alt229=19;
				}
				break;
			case K_DATE:
				{
				alt229=20;
				}
				break;
			case K_TIME:
				{
				alt229=21;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return t;}
				NoViableAltException nvae =
					new NoViableAltException("", 229, 0, input);
				throw nvae;
			}
			switch (alt229) {
				case 1 :
					// Parser.g:1741:7: K_ASCII
					{
					match(input,K_ASCII,FOLLOW_K_ASCII_in_native_type13110); if (state.failed) return t;
					if ( state.backtracking==0 ) { t = CQL3Type.Native.ASCII; }
					}
					break;
				case 2 :
					// Parser.g:1742:7: K_BIGINT
					{
					match(input,K_BIGINT,FOLLOW_K_BIGINT_in_native_type13124); if (state.failed) return t;
					if ( state.backtracking==0 ) { t = CQL3Type.Native.BIGINT; }
					}
					break;
				case 3 :
					// Parser.g:1743:7: K_BLOB
					{
					match(input,K_BLOB,FOLLOW_K_BLOB_in_native_type13137); if (state.failed) return t;
					if ( state.backtracking==0 ) { t = CQL3Type.Native.BLOB; }
					}
					break;
				case 4 :
					// Parser.g:1744:7: K_BOOLEAN
					{
					match(input,K_BOOLEAN,FOLLOW_K_BOOLEAN_in_native_type13152); if (state.failed) return t;
					if ( state.backtracking==0 ) { t = CQL3Type.Native.BOOLEAN; }
					}
					break;
				case 5 :
					// Parser.g:1745:7: K_COUNTER
					{
					match(input,K_COUNTER,FOLLOW_K_COUNTER_in_native_type13164); if (state.failed) return t;
					if ( state.backtracking==0 ) { t = CQL3Type.Native.COUNTER; }
					}
					break;
				case 6 :
					// Parser.g:1746:7: K_DECIMAL
					{
					match(input,K_DECIMAL,FOLLOW_K_DECIMAL_in_native_type13176); if (state.failed) return t;
					if ( state.backtracking==0 ) { t = CQL3Type.Native.DECIMAL; }
					}
					break;
				case 7 :
					// Parser.g:1747:7: K_DOUBLE
					{
					match(input,K_DOUBLE,FOLLOW_K_DOUBLE_in_native_type13188); if (state.failed) return t;
					if ( state.backtracking==0 ) { t = CQL3Type.Native.DOUBLE; }
					}
					break;
				case 8 :
					// Parser.g:1748:7: K_DURATION
					{
					match(input,K_DURATION,FOLLOW_K_DURATION_in_native_type13201); if (state.failed) return t;
					if ( state.backtracking==0 ) { t = CQL3Type.Native.DURATION; }
					}
					break;
				case 9 :
					// Parser.g:1749:7: K_FLOAT
					{
					match(input,K_FLOAT,FOLLOW_K_FLOAT_in_native_type13214); if (state.failed) return t;
					if ( state.backtracking==0 ) { t = CQL3Type.Native.FLOAT; }
					}
					break;
				case 10 :
					// Parser.g:1750:7: K_INET
					{
					match(input,K_INET,FOLLOW_K_INET_in_native_type13228); if (state.failed) return t;
					if ( state.backtracking==0 ) { t = CQL3Type.Native.INET;}
					}
					break;
				case 11 :
					// Parser.g:1751:7: K_INT
					{
					match(input,K_INT,FOLLOW_K_INT_in_native_type13243); if (state.failed) return t;
					if ( state.backtracking==0 ) { t = CQL3Type.Native.INT; }
					}
					break;
				case 12 :
					// Parser.g:1752:7: K_SMALLINT
					{
					match(input,K_SMALLINT,FOLLOW_K_SMALLINT_in_native_type13259); if (state.failed) return t;
					if ( state.backtracking==0 ) { t = CQL3Type.Native.SMALLINT; }
					}
					break;
				case 13 :
					// Parser.g:1753:7: K_TEXT
					{
					match(input,K_TEXT,FOLLOW_K_TEXT_in_native_type13270); if (state.failed) return t;
					if ( state.backtracking==0 ) { t = CQL3Type.Native.TEXT; }
					}
					break;
				case 14 :
					// Parser.g:1754:7: K_TIMESTAMP
					{
					match(input,K_TIMESTAMP,FOLLOW_K_TIMESTAMP_in_native_type13285); if (state.failed) return t;
					if ( state.backtracking==0 ) { t = CQL3Type.Native.TIMESTAMP; }
					}
					break;
				case 15 :
					// Parser.g:1755:7: K_TINYINT
					{
					match(input,K_TINYINT,FOLLOW_K_TINYINT_in_native_type13295); if (state.failed) return t;
					if ( state.backtracking==0 ) { t = CQL3Type.Native.TINYINT; }
					}
					break;
				case 16 :
					// Parser.g:1756:7: K_UUID
					{
					match(input,K_UUID,FOLLOW_K_UUID_in_native_type13307); if (state.failed) return t;
					if ( state.backtracking==0 ) { t = CQL3Type.Native.UUID; }
					}
					break;
				case 17 :
					// Parser.g:1757:7: K_VARCHAR
					{
					match(input,K_VARCHAR,FOLLOW_K_VARCHAR_in_native_type13322); if (state.failed) return t;
					if ( state.backtracking==0 ) { t = CQL3Type.Native.VARCHAR; }
					}
					break;
				case 18 :
					// Parser.g:1758:7: K_VARINT
					{
					match(input,K_VARINT,FOLLOW_K_VARINT_in_native_type13334); if (state.failed) return t;
					if ( state.backtracking==0 ) { t = CQL3Type.Native.VARINT; }
					}
					break;
				case 19 :
					// Parser.g:1759:7: K_TIMEUUID
					{
					match(input,K_TIMEUUID,FOLLOW_K_TIMEUUID_in_native_type13347); if (state.failed) return t;
					if ( state.backtracking==0 ) { t = CQL3Type.Native.TIMEUUID; }
					}
					break;
				case 20 :
					// Parser.g:1760:7: K_DATE
					{
					match(input,K_DATE,FOLLOW_K_DATE_in_native_type13358); if (state.failed) return t;
					if ( state.backtracking==0 ) { t = CQL3Type.Native.DATE; }
					}
					break;
				case 21 :
					// Parser.g:1761:7: K_TIME
					{
					match(input,K_TIME,FOLLOW_K_TIME_in_native_type13373); if (state.failed) return t;
					if ( state.backtracking==0 ) { t = CQL3Type.Native.TIME; }
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return t;
	}
	// $ANTLR end "native_type"



	// $ANTLR start "collection_type"
	// Parser.g:1764:1: collection_type returns [CQL3Type.Raw pt] : ( K_MAP '<' t1= comparatorType ',' t2= comparatorType '>' | K_LIST '<' t= comparatorType '>' | K_SET '<' t= comparatorType '>' );
	public final CQL3Type.Raw collection_type() throws RecognitionException {
		CQL3Type.Raw pt = null;


		CQL3Type.Raw t1 =null;
		CQL3Type.Raw t2 =null;
		CQL3Type.Raw t =null;

		try {
			// Parser.g:1765:5: ( K_MAP '<' t1= comparatorType ',' t2= comparatorType '>' | K_LIST '<' t= comparatorType '>' | K_SET '<' t= comparatorType '>' )
			int alt230=3;
			switch ( input.LA(1) ) {
			case K_MAP:
				{
				alt230=1;
				}
				break;
			case K_LIST:
				{
				alt230=2;
				}
				break;
			case K_SET:
				{
				alt230=3;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return pt;}
				NoViableAltException nvae =
					new NoViableAltException("", 230, 0, input);
				throw nvae;
			}
			switch (alt230) {
				case 1 :
					// Parser.g:1765:7: K_MAP '<' t1= comparatorType ',' t2= comparatorType '>'
					{
					match(input,K_MAP,FOLLOW_K_MAP_in_collection_type13401); if (state.failed) return pt;
					match(input,201,FOLLOW_201_in_collection_type13404); if (state.failed) return pt;
					pushFollow(FOLLOW_comparatorType_in_collection_type13408);
					t1=comparatorType();
					state._fsp--;
					if (state.failed) return pt;
					match(input,194,FOLLOW_194_in_collection_type13410); if (state.failed) return pt;
					pushFollow(FOLLOW_comparatorType_in_collection_type13414);
					t2=comparatorType();
					state._fsp--;
					if (state.failed) return pt;
					match(input,204,FOLLOW_204_in_collection_type13416); if (state.failed) return pt;
					if ( state.backtracking==0 ) {
					            // if we can't parse either t1 or t2, antlr will "recover" and we may have t1 or t2 null.
					            if (t1 != null && t2 != null)
					                pt = CQL3Type.Raw.map(t1, t2);
					        }
					}
					break;
				case 2 :
					// Parser.g:1771:7: K_LIST '<' t= comparatorType '>'
					{
					match(input,K_LIST,FOLLOW_K_LIST_in_collection_type13434); if (state.failed) return pt;
					match(input,201,FOLLOW_201_in_collection_type13436); if (state.failed) return pt;
					pushFollow(FOLLOW_comparatorType_in_collection_type13440);
					t=comparatorType();
					state._fsp--;
					if (state.failed) return pt;
					match(input,204,FOLLOW_204_in_collection_type13442); if (state.failed) return pt;
					if ( state.backtracking==0 ) { if (t != null) pt = CQL3Type.Raw.list(t); }
					}
					break;
				case 3 :
					// Parser.g:1773:7: K_SET '<' t= comparatorType '>'
					{
					match(input,K_SET,FOLLOW_K_SET_in_collection_type13460); if (state.failed) return pt;
					match(input,201,FOLLOW_201_in_collection_type13463); if (state.failed) return pt;
					pushFollow(FOLLOW_comparatorType_in_collection_type13467);
					t=comparatorType();
					state._fsp--;
					if (state.failed) return pt;
					match(input,204,FOLLOW_204_in_collection_type13469); if (state.failed) return pt;
					if ( state.backtracking==0 ) { if (t != null) pt = CQL3Type.Raw.set(t); }
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return pt;
	}
	// $ANTLR end "collection_type"



	// $ANTLR start "tuple_type"
	// Parser.g:1777:1: tuple_type returns [CQL3Type.Raw t] : K_TUPLE '<' t1= comparatorType ( ',' tn= comparatorType )* '>' ;
	public final CQL3Type.Raw tuple_type() throws RecognitionException {
		CQL3Type.Raw t = null;


		CQL3Type.Raw t1 =null;
		CQL3Type.Raw tn =null;

		List<CQL3Type.Raw> types = new ArrayList<>();
		try {
			// Parser.g:1780:5: ( K_TUPLE '<' t1= comparatorType ( ',' tn= comparatorType )* '>' )
			// Parser.g:1780:7: K_TUPLE '<' t1= comparatorType ( ',' tn= comparatorType )* '>'
			{
			match(input,K_TUPLE,FOLLOW_K_TUPLE_in_tuple_type13518); if (state.failed) return t;
			match(input,201,FOLLOW_201_in_tuple_type13520); if (state.failed) return t;
			pushFollow(FOLLOW_comparatorType_in_tuple_type13524);
			t1=comparatorType();
			state._fsp--;
			if (state.failed) return t;
			if ( state.backtracking==0 ) { types.add(t1); }
			// Parser.g:1780:56: ( ',' tn= comparatorType )*
			loop231:
			while (true) {
				int alt231=2;
				int LA231_0 = input.LA(1);
				if ( (LA231_0==194) ) {
					alt231=1;
				}

				switch (alt231) {
				case 1 :
					// Parser.g:1780:57: ',' tn= comparatorType
					{
					match(input,194,FOLLOW_194_in_tuple_type13529); if (state.failed) return t;
					pushFollow(FOLLOW_comparatorType_in_tuple_type13533);
					tn=comparatorType();
					state._fsp--;
					if (state.failed) return t;
					if ( state.backtracking==0 ) { types.add(tn); }
					}
					break;

				default :
					break loop231;
				}
			}

			match(input,204,FOLLOW_204_in_tuple_type13539); if (state.failed) return t;
			}

			if ( state.backtracking==0 ) {t = CQL3Type.Raw.tuple(types);}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return t;
	}
	// $ANTLR end "tuple_type"


	public static class username_return extends ParserRuleReturnScope {
	};


	// $ANTLR start "username"
	// Parser.g:1783:1: username : ( IDENT | STRING_LITERAL | QUOTED_NAME );
	public final Cql_Parser.username_return username() throws RecognitionException {
		Cql_Parser.username_return retval = new Cql_Parser.username_return();
		retval.start = input.LT(1);

		try {
			// Parser.g:1784:5: ( IDENT | STRING_LITERAL | QUOTED_NAME )
			int alt232=3;
			switch ( input.LA(1) ) {
			case IDENT:
				{
				alt232=1;
				}
				break;
			case STRING_LITERAL:
				{
				alt232=2;
				}
				break;
			case QUOTED_NAME:
				{
				alt232=3;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 232, 0, input);
				throw nvae;
			}
			switch (alt232) {
				case 1 :
					// Parser.g:1784:7: IDENT
					{
					match(input,IDENT,FOLLOW_IDENT_in_username13556); if (state.failed) return retval;
					}
					break;
				case 2 :
					// Parser.g:1785:7: STRING_LITERAL
					{
					match(input,STRING_LITERAL,FOLLOW_STRING_LITERAL_in_username13564); if (state.failed) return retval;
					}
					break;
				case 3 :
					// Parser.g:1786:7: QUOTED_NAME
					{
					match(input,QUOTED_NAME,FOLLOW_QUOTED_NAME_in_username13572); if (state.failed) return retval;
					if ( state.backtracking==0 ) { addRecognitionError("Quoted strings are are not supported for user names and USER is deprecated, please use ROLE");}
					}
					break;

			}
			retval.stop = input.LT(-1);

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "username"


	public static class mbean_return extends ParserRuleReturnScope {
	};


	// $ANTLR start "mbean"
	// Parser.g:1789:1: mbean : STRING_LITERAL ;
	public final Cql_Parser.mbean_return mbean() throws RecognitionException {
		Cql_Parser.mbean_return retval = new Cql_Parser.mbean_return();
		retval.start = input.LT(1);

		try {
			// Parser.g:1790:5: ( STRING_LITERAL )
			// Parser.g:1790:7: STRING_LITERAL
			{
			match(input,STRING_LITERAL,FOLLOW_STRING_LITERAL_in_mbean13591); if (state.failed) return retval;
			}

			retval.stop = input.LT(-1);

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "mbean"



	// $ANTLR start "non_type_ident"
	// Parser.g:1795:1: non_type_ident returns [ColumnIdentifier id] : (t= IDENT |t= QUOTED_NAME |k= basic_unreserved_keyword |kk= K_KEY );
	public final ColumnIdentifier non_type_ident() throws RecognitionException {
		ColumnIdentifier id = null;


		Token t=null;
		Token kk=null;
		String k =null;

		try {
			// Parser.g:1796:5: (t= IDENT |t= QUOTED_NAME |k= basic_unreserved_keyword |kk= K_KEY )
			int alt233=4;
			switch ( input.LA(1) ) {
			case IDENT:
				{
				alt233=1;
				}
				break;
			case QUOTED_NAME:
				{
				alt233=2;
				}
				break;
			case K_AGGREGATE:
			case K_ALL:
			case K_AS:
			case K_CALLED:
			case K_CLUSTERING:
			case K_COMPACT:
			case K_CONTAINS:
			case K_CUSTOM:
			case K_EXISTS:
			case K_FILTERING:
			case K_FINALFUNC:
			case K_FROZEN:
			case K_FUNCTION:
			case K_FUNCTIONS:
			case K_GROUP:
			case K_INITCOND:
			case K_INPUT:
			case K_KEYS:
			case K_KEYSPACES:
			case K_LANGUAGE:
			case K_LIKE:
			case K_LIST:
			case K_LOGIN:
			case K_MAP:
			case K_NOLOGIN:
			case K_NOSUPERUSER:
			case K_OPTIONS:
			case K_PARTITION:
			case K_PASSWORD:
			case K_PER:
			case K_PERMISSION:
			case K_PERMISSIONS:
			case K_RETURNS:
			case K_ROLE:
			case K_ROLES:
			case K_SFUNC:
			case K_STATIC:
			case K_STORAGE:
			case K_STYPE:
			case K_SUPERUSER:
			case K_TRIGGER:
			case K_TUPLE:
			case K_TYPE:
			case K_USER:
			case K_USERS:
			case K_VALUES:
				{
				alt233=3;
				}
				break;
			case K_KEY:
				{
				alt233=4;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return id;}
				NoViableAltException nvae =
					new NoViableAltException("", 233, 0, input);
				throw nvae;
			}
			switch (alt233) {
				case 1 :
					// Parser.g:1796:7: t= IDENT
					{
					t=(Token)match(input,IDENT,FOLLOW_IDENT_in_non_type_ident13616); if (state.failed) return id;
					if ( state.backtracking==0 ) { if (reservedTypeNames.contains((t!=null?t.getText():null))) addRecognitionError("Invalid (reserved) user type name " + (t!=null?t.getText():null)); id = new ColumnIdentifier((t!=null?t.getText():null), false); }
					}
					break;
				case 2 :
					// Parser.g:1797:7: t= QUOTED_NAME
					{
					t=(Token)match(input,QUOTED_NAME,FOLLOW_QUOTED_NAME_in_non_type_ident13647); if (state.failed) return id;
					if ( state.backtracking==0 ) { id = new ColumnIdentifier((t!=null?t.getText():null), true); }
					}
					break;
				case 3 :
					// Parser.g:1798:7: k= basic_unreserved_keyword
					{
					pushFollow(FOLLOW_basic_unreserved_keyword_in_non_type_ident13672);
					k=basic_unreserved_keyword();
					state._fsp--;
					if (state.failed) return id;
					if ( state.backtracking==0 ) { id = new ColumnIdentifier(k, false); }
					}
					break;
				case 4 :
					// Parser.g:1799:7: kk= K_KEY
					{
					kk=(Token)match(input,K_KEY,FOLLOW_K_KEY_in_non_type_ident13684); if (state.failed) return id;
					if ( state.backtracking==0 ) { id = new ColumnIdentifier((kk!=null?kk.getText():null), false); }
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return id;
	}
	// $ANTLR end "non_type_ident"



	// $ANTLR start "unreserved_keyword"
	// Parser.g:1802:1: unreserved_keyword returns [String str] : (u= unreserved_function_keyword |k= ( K_TTL | K_COUNT | K_WRITETIME | K_KEY | K_CAST | K_JSON | K_DISTINCT ) );
	public final String unreserved_keyword() throws RecognitionException {
		String str = null;


		Token k=null;
		String u =null;

		try {
			// Parser.g:1803:5: (u= unreserved_function_keyword |k= ( K_TTL | K_COUNT | K_WRITETIME | K_KEY | K_CAST | K_JSON | K_DISTINCT ) )
			int alt234=2;
			int LA234_0 = input.LA(1);
			if ( ((LA234_0 >= K_AGGREGATE && LA234_0 <= K_ALL)||LA234_0==K_AS||LA234_0==K_ASCII||(LA234_0 >= K_BIGINT && LA234_0 <= K_BOOLEAN)||LA234_0==K_CALLED||LA234_0==K_CLUSTERING||(LA234_0 >= K_COMPACT && LA234_0 <= K_CONTAINS)||LA234_0==K_COUNTER||LA234_0==K_CUSTOM||(LA234_0 >= K_DATE && LA234_0 <= K_DECIMAL)||LA234_0==K_DOUBLE||LA234_0==K_DURATION||(LA234_0 >= K_EXISTS && LA234_0 <= K_FLOAT)||LA234_0==K_FROZEN||(LA234_0 >= K_FUNCTION && LA234_0 <= K_FUNCTIONS)||LA234_0==K_GROUP||(LA234_0 >= K_INET && LA234_0 <= K_INPUT)||LA234_0==K_INT||LA234_0==K_KEYS||(LA234_0 >= K_KEYSPACES && LA234_0 <= K_LIKE)||(LA234_0 >= K_LIST && LA234_0 <= K_MAP)||LA234_0==K_NOLOGIN||LA234_0==K_NOSUPERUSER||LA234_0==K_OPTIONS||(LA234_0 >= K_PARTITION && LA234_0 <= K_PERMISSIONS)||LA234_0==K_RETURNS||(LA234_0 >= K_ROLE && LA234_0 <= K_ROLES)||(LA234_0 >= K_SFUNC && LA234_0 <= K_TINYINT)||LA234_0==K_TRIGGER||(LA234_0 >= K_TUPLE && LA234_0 <= K_TYPE)||(LA234_0 >= K_USER && LA234_0 <= K_USERS)||(LA234_0 >= K_UUID && LA234_0 <= K_VARINT)) ) {
				alt234=1;
			}
			else if ( (LA234_0==K_CAST||LA234_0==K_COUNT||LA234_0==K_DISTINCT||(LA234_0 >= K_JSON && LA234_0 <= K_KEY)||LA234_0==K_TTL||LA234_0==K_WRITETIME) ) {
				alt234=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return str;}
				NoViableAltException nvae =
					new NoViableAltException("", 234, 0, input);
				throw nvae;
			}

			switch (alt234) {
				case 1 :
					// Parser.g:1803:7: u= unreserved_function_keyword
					{
					pushFollow(FOLLOW_unreserved_function_keyword_in_unreserved_keyword13727);
					u=unreserved_function_keyword();
					state._fsp--;
					if (state.failed) return str;
					if ( state.backtracking==0 ) { str = u; }
					}
					break;
				case 2 :
					// Parser.g:1804:7: k= ( K_TTL | K_COUNT | K_WRITETIME | K_KEY | K_CAST | K_JSON | K_DISTINCT )
					{
					k=input.LT(1);
					if ( input.LA(1)==K_CAST||input.LA(1)==K_COUNT||input.LA(1)==K_DISTINCT||(input.LA(1) >= K_JSON && input.LA(1) <= K_KEY)||input.LA(1)==K_TTL||input.LA(1)==K_WRITETIME ) {
						input.consume();
						state.errorRecovery=false;
						state.failed=false;
					}
					else {
						if (state.backtracking>0) {state.failed=true; return str;}
						MismatchedSetException mse = new MismatchedSetException(null,input);
						throw mse;
					}
					if ( state.backtracking==0 ) { str = (k!=null?k.getText():null); }
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return str;
	}
	// $ANTLR end "unreserved_keyword"



	// $ANTLR start "unreserved_function_keyword"
	// Parser.g:1807:1: unreserved_function_keyword returns [String str] : (u= basic_unreserved_keyword |t= native_type );
	public final String unreserved_function_keyword() throws RecognitionException {
		String str = null;


		String u =null;
		CQL3Type t =null;

		try {
			// Parser.g:1808:5: (u= basic_unreserved_keyword |t= native_type )
			int alt235=2;
			int LA235_0 = input.LA(1);
			if ( ((LA235_0 >= K_AGGREGATE && LA235_0 <= K_ALL)||LA235_0==K_AS||LA235_0==K_CALLED||LA235_0==K_CLUSTERING||(LA235_0 >= K_COMPACT && LA235_0 <= K_CONTAINS)||LA235_0==K_CUSTOM||(LA235_0 >= K_EXISTS && LA235_0 <= K_FINALFUNC)||LA235_0==K_FROZEN||(LA235_0 >= K_FUNCTION && LA235_0 <= K_FUNCTIONS)||LA235_0==K_GROUP||(LA235_0 >= K_INITCOND && LA235_0 <= K_INPUT)||LA235_0==K_KEYS||(LA235_0 >= K_KEYSPACES && LA235_0 <= K_LIKE)||(LA235_0 >= K_LIST && LA235_0 <= K_MAP)||LA235_0==K_NOLOGIN||LA235_0==K_NOSUPERUSER||LA235_0==K_OPTIONS||(LA235_0 >= K_PARTITION && LA235_0 <= K_PERMISSIONS)||LA235_0==K_RETURNS||(LA235_0 >= K_ROLE && LA235_0 <= K_ROLES)||LA235_0==K_SFUNC||(LA235_0 >= K_STATIC && LA235_0 <= K_SUPERUSER)||LA235_0==K_TRIGGER||(LA235_0 >= K_TUPLE && LA235_0 <= K_TYPE)||(LA235_0 >= K_USER && LA235_0 <= K_USERS)||LA235_0==K_VALUES) ) {
				alt235=1;
			}
			else if ( (LA235_0==K_ASCII||(LA235_0 >= K_BIGINT && LA235_0 <= K_BOOLEAN)||LA235_0==K_COUNTER||(LA235_0 >= K_DATE && LA235_0 <= K_DECIMAL)||LA235_0==K_DOUBLE||LA235_0==K_DURATION||LA235_0==K_FLOAT||LA235_0==K_INET||LA235_0==K_INT||LA235_0==K_SMALLINT||(LA235_0 >= K_TEXT && LA235_0 <= K_TINYINT)||LA235_0==K_UUID||(LA235_0 >= K_VARCHAR && LA235_0 <= K_VARINT)) ) {
				alt235=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return str;}
				NoViableAltException nvae =
					new NoViableAltException("", 235, 0, input);
				throw nvae;
			}

			switch (alt235) {
				case 1 :
					// Parser.g:1808:7: u= basic_unreserved_keyword
					{
					pushFollow(FOLLOW_basic_unreserved_keyword_in_unreserved_function_keyword13794);
					u=basic_unreserved_keyword();
					state._fsp--;
					if (state.failed) return str;
					if ( state.backtracking==0 ) { str = u; }
					}
					break;
				case 2 :
					// Parser.g:1809:7: t= native_type
					{
					pushFollow(FOLLOW_native_type_in_unreserved_function_keyword13806);
					t=native_type();
					state._fsp--;
					if (state.failed) return str;
					if ( state.backtracking==0 ) { str = t.toString(); }
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return str;
	}
	// $ANTLR end "unreserved_function_keyword"



	// $ANTLR start "basic_unreserved_keyword"
	// Parser.g:1812:1: basic_unreserved_keyword returns [String str] : k= ( K_KEYS | K_AS | K_CLUSTERING | K_COMPACT | K_STORAGE | K_TYPE | K_VALUES | K_MAP | K_LIST | K_FILTERING | K_PERMISSION | K_PERMISSIONS | K_KEYSPACES | K_ALL | K_USER | K_USERS | K_ROLE | K_ROLES | K_SUPERUSER | K_NOSUPERUSER | K_LOGIN | K_NOLOGIN | K_OPTIONS | K_PASSWORD | K_EXISTS | K_CUSTOM | K_TRIGGER | K_CONTAINS | K_STATIC | K_FROZEN | K_TUPLE | K_FUNCTION | K_FUNCTIONS | K_AGGREGATE | K_SFUNC | K_STYPE | K_FINALFUNC | K_INITCOND | K_RETURNS | K_LANGUAGE | K_CALLED | K_INPUT | K_LIKE | K_PER | K_PARTITION | K_GROUP ) ;
	public final String basic_unreserved_keyword() throws RecognitionException {
		String str = null;


		Token k=null;

		try {
			// Parser.g:1813:5: (k= ( K_KEYS | K_AS | K_CLUSTERING | K_COMPACT | K_STORAGE | K_TYPE | K_VALUES | K_MAP | K_LIST | K_FILTERING | K_PERMISSION | K_PERMISSIONS | K_KEYSPACES | K_ALL | K_USER | K_USERS | K_ROLE | K_ROLES | K_SUPERUSER | K_NOSUPERUSER | K_LOGIN | K_NOLOGIN | K_OPTIONS | K_PASSWORD | K_EXISTS | K_CUSTOM | K_TRIGGER | K_CONTAINS | K_STATIC | K_FROZEN | K_TUPLE | K_FUNCTION | K_FUNCTIONS | K_AGGREGATE | K_SFUNC | K_STYPE | K_FINALFUNC | K_INITCOND | K_RETURNS | K_LANGUAGE | K_CALLED | K_INPUT | K_LIKE | K_PER | K_PARTITION | K_GROUP ) )
			// Parser.g:1813:7: k= ( K_KEYS | K_AS | K_CLUSTERING | K_COMPACT | K_STORAGE | K_TYPE | K_VALUES | K_MAP | K_LIST | K_FILTERING | K_PERMISSION | K_PERMISSIONS | K_KEYSPACES | K_ALL | K_USER | K_USERS | K_ROLE | K_ROLES | K_SUPERUSER | K_NOSUPERUSER | K_LOGIN | K_NOLOGIN | K_OPTIONS | K_PASSWORD | K_EXISTS | K_CUSTOM | K_TRIGGER | K_CONTAINS | K_STATIC | K_FROZEN | K_TUPLE | K_FUNCTION | K_FUNCTIONS | K_AGGREGATE | K_SFUNC | K_STYPE | K_FINALFUNC | K_INITCOND | K_RETURNS | K_LANGUAGE | K_CALLED | K_INPUT | K_LIKE | K_PER | K_PARTITION | K_GROUP )
			{
			k=input.LT(1);
			if ( (input.LA(1) >= K_AGGREGATE && input.LA(1) <= K_ALL)||input.LA(1)==K_AS||input.LA(1)==K_CALLED||input.LA(1)==K_CLUSTERING||(input.LA(1) >= K_COMPACT && input.LA(1) <= K_CONTAINS)||input.LA(1)==K_CUSTOM||(input.LA(1) >= K_EXISTS && input.LA(1) <= K_FINALFUNC)||input.LA(1)==K_FROZEN||(input.LA(1) >= K_FUNCTION && input.LA(1) <= K_FUNCTIONS)||input.LA(1)==K_GROUP||(input.LA(1) >= K_INITCOND && input.LA(1) <= K_INPUT)||input.LA(1)==K_KEYS||(input.LA(1) >= K_KEYSPACES && input.LA(1) <= K_LIKE)||(input.LA(1) >= K_LIST && input.LA(1) <= K_MAP)||input.LA(1)==K_NOLOGIN||input.LA(1)==K_NOSUPERUSER||input.LA(1)==K_OPTIONS||(input.LA(1) >= K_PARTITION && input.LA(1) <= K_PERMISSIONS)||input.LA(1)==K_RETURNS||(input.LA(1) >= K_ROLE && input.LA(1) <= K_ROLES)||input.LA(1)==K_SFUNC||(input.LA(1) >= K_STATIC && input.LA(1) <= K_SUPERUSER)||input.LA(1)==K_TRIGGER||(input.LA(1) >= K_TUPLE && input.LA(1) <= K_TYPE)||(input.LA(1) >= K_USER && input.LA(1) <= K_USERS)||input.LA(1)==K_VALUES ) {
				input.consume();
				state.errorRecovery=false;
				state.failed=false;
			}
			else {
				if (state.backtracking>0) {state.failed=true; return str;}
				MismatchedSetException mse = new MismatchedSetException(null,input);
				throw mse;
			}
			if ( state.backtracking==0 ) { str = (k!=null?k.getText():null); }
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return str;
	}
	// $ANTLR end "basic_unreserved_keyword"

	// $ANTLR start synpred1_Parser
	public final void synpred1_Parser_fragment() throws RecognitionException {
		// Parser.g:275:9: ( K_JSON selectClause )
		// Parser.g:275:10: K_JSON selectClause
		{
		match(input,K_JSON,FOLLOW_K_JSON_in_synpred1_Parser1062); if (state.failed) return;
		pushFollow(FOLLOW_selectClause_in_synpred1_Parser1064);
		selectClause();
		state._fsp--;
		if (state.failed) return;
		}

	}
	// $ANTLR end synpred1_Parser

	// $ANTLR start synpred2_Parser
	public final void synpred2_Parser_fragment() throws RecognitionException {
		// Parser.g:297:7: ( K_DISTINCT selectors )
		// Parser.g:297:8: K_DISTINCT selectors
		{
		match(input,K_DISTINCT,FOLLOW_K_DISTINCT_in_synpred2_Parser1265); if (state.failed) return;
		pushFollow(FOLLOW_selectors_in_synpred2_Parser1267);
		selectors();
		state._fsp--;
		if (state.failed) return;
		}

	}
	// $ANTLR end synpred2_Parser

	// $ANTLR start synpred3_Parser
	public final void synpred3_Parser_fragment() throws RecognitionException {
		// Parser.g:331:7: ( selectionGroupWithField )
		// Parser.g:331:8: selectionGroupWithField
		{
		pushFollow(FOLLOW_selectionGroupWithField_in_synpred3_Parser1596);
		selectionGroupWithField();
		state._fsp--;
		if (state.failed) return;
		}

	}
	// $ANTLR end synpred3_Parser

	// $ANTLR start synpred4_Parser
	public final void synpred4_Parser_fragment() throws RecognitionException {
		// Parser.g:365:7: ( selectionTypeHint )
		// Parser.g:365:8: selectionTypeHint
		{
		pushFollow(FOLLOW_selectionTypeHint_in_synpred4_Parser1883);
		selectionTypeHint();
		state._fsp--;
		if (state.failed) return;
		}

	}
	// $ANTLR end synpred4_Parser

	// Delegated rules

	public final boolean synpred2_Parser() {
		state.backtracking++;
		int start = input.mark();
		try {
			synpred2_Parser_fragment(); // can never throw exception
		} catch (RecognitionException re) {
			System.err.println("impossible: "+re);
		}
		boolean success = !state.failed;
		input.rewind(start);
		state.backtracking--;
		state.failed=false;
		return success;
	}
	public final boolean synpred1_Parser() {
		state.backtracking++;
		int start = input.mark();
		try {
			synpred1_Parser_fragment(); // can never throw exception
		} catch (RecognitionException re) {
			System.err.println("impossible: "+re);
		}
		boolean success = !state.failed;
		input.rewind(start);
		state.backtracking--;
		state.failed=false;
		return success;
	}
	public final boolean synpred3_Parser() {
		state.backtracking++;
		int start = input.mark();
		try {
			synpred3_Parser_fragment(); // can never throw exception
		} catch (RecognitionException re) {
			System.err.println("impossible: "+re);
		}
		boolean success = !state.failed;
		input.rewind(start);
		state.backtracking--;
		state.failed=false;
		return success;
	}
	public final boolean synpred4_Parser() {
		state.backtracking++;
		int start = input.mark();
		try {
			synpred4_Parser_fragment(); // can never throw exception
		} catch (RecognitionException re) {
			System.err.println("impossible: "+re);
		}
		boolean success = !state.failed;
		input.rewind(start);
		state.backtracking--;
		state.failed=false;
		return success;
	}


	protected DFA1 dfa1 = new DFA1(this);
	protected DFA2 dfa2 = new DFA2(this);
	protected DFA11 dfa11 = new DFA11(this);
	protected DFA17 dfa17 = new DFA17(this);
	protected DFA22 dfa22 = new DFA22(this);
	protected DFA30 dfa30 = new DFA30(this);
	protected DFA31 dfa31 = new DFA31(this);
	protected DFA61 dfa61 = new DFA61(this);
	protected DFA174 dfa174 = new DFA174(this);
	protected DFA175 dfa175 = new DFA175(this);
	protected DFA193 dfa193 = new DFA193(this);
	protected DFA195 dfa195 = new DFA195(this);
	protected DFA197 dfa197 = new DFA197(this);
	protected DFA199 dfa199 = new DFA199(this);
	protected DFA202 dfa202 = new DFA202(this);
	protected DFA205 dfa205 = new DFA205(this);
	protected DFA213 dfa213 = new DFA213(this);
	protected DFA218 dfa218 = new DFA218(this);
	protected DFA217 dfa217 = new DFA217(this);
	protected DFA228 dfa228 = new DFA228(this);
	static final String DFA1_eotS =
		"\63\uffff";
	static final String DFA1_eofS =
		"\63\uffff";
	static final String DFA1_minS =
		"\1\40\7\uffff\2\35\1\60\2\27\1\36\10\uffff\1\175\22\uffff\1\160\2\uffff"+
		"\1\110\5\uffff\1\35";
	static final String DFA1_maxS =
		"\1\u0099\7\uffff\3\u009a\2\u00b2\1\u009b\10\uffff\1\175\22\uffff\1\u008f"+
		"\2\uffff\1\170\5\uffff\1\113";
	static final String DFA1_acceptS =
		"\1\uffff\1\1\1\2\1\3\1\4\1\5\1\6\1\7\6\uffff\1\10\1\11\1\23\1\27\1\31"+
		"\1\40\1\46\1\12\1\uffff\1\34\1\36\1\13\1\14\1\15\1\25\1\30\1\33\1\35\1"+
		"\37\1\42\1\47\1\16\1\17\1\24\1\32\1\41\1\50\1\uffff\1\20\1\44\1\uffff"+
		"\1\21\1\45\1\26\1\43\1\22\1\uffff";
	static final String DFA1_specialS =
		"\63\uffff}>";
	static final String[] DFA1_transitionS = {
			"\1\12\7\uffff\1\4\14\uffff\1\10\5\uffff\1\5\4\uffff\1\11\14\uffff\1\13"+
			"\7\uffff\1\2\13\uffff\1\15\35\uffff\1\14\2\uffff\1\1\17\uffff\1\7\5\uffff"+
			"\1\3\1\6",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"\1\30\22\uffff\1\17\5\uffff\1\25\24\uffff\1\27\5\uffff\1\25\12\uffff"+
			"\1\16\7\uffff\1\24\15\uffff\1\26\15\uffff\1\23\20\uffff\1\21\3\uffff"+
			"\1\22\4\uffff\1\20",
			"\1\40\22\uffff\1\32\32\uffff\1\37\5\uffff\1\33\12\uffff\1\31\7\uffff"+
			"\1\42\33\uffff\1\41\20\uffff\1\35\3\uffff\1\36\4\uffff\1\34",
			"\1\43\53\uffff\1\44\7\uffff\1\50\33\uffff\1\47\24\uffff\1\46\4\uffff"+
			"\1\45",
			"\1\53\5\uffff\1\53\1\51\1\uffff\1\52\2\uffff\1\53\1\uffff\1\53\1\52"+
			"\2\uffff\3\53\1\uffff\3\53\1\uffff\4\53\1\52\1\53\1\uffff\2\53\3\uffff"+
			"\1\52\2\53\1\52\1\53\1\uffff\1\52\4\53\1\uffff\1\53\1\uffff\2\53\1\uffff"+
			"\1\53\3\uffff\3\53\1\uffff\1\53\2\uffff\3\53\1\uffff\3\53\1\uffff\3\53"+
			"\3\uffff\1\52\2\uffff\1\53\1\uffff\1\53\4\uffff\1\53\2\uffff\5\53\5\uffff"+
			"\1\53\1\uffff\2\53\1\52\1\uffff\13\53\2\uffff\1\53\1\uffff\3\53\4\uffff"+
			"\2\53\1\uffff\4\53\3\uffff\1\53\10\uffff\2\53\3\uffff\1\53",
			"\1\56\5\uffff\1\56\1\54\1\uffff\1\55\2\uffff\1\56\1\uffff\1\56\1\55"+
			"\2\uffff\3\56\1\uffff\3\56\1\uffff\4\56\1\55\1\56\1\uffff\2\56\3\uffff"+
			"\1\55\2\56\1\55\1\56\1\uffff\1\55\4\56\1\uffff\1\56\1\uffff\2\56\1\uffff"+
			"\1\56\3\uffff\3\56\1\uffff\1\56\2\uffff\3\56\1\uffff\3\56\1\uffff\3\56"+
			"\3\uffff\1\55\2\uffff\1\56\1\uffff\1\56\4\uffff\1\56\2\uffff\5\56\5\uffff"+
			"\1\56\1\uffff\2\56\1\55\1\uffff\13\56\2\uffff\1\56\1\uffff\3\56\4\uffff"+
			"\2\56\1\uffff\4\56\3\uffff\1\56\10\uffff\2\56\3\uffff\1\56",
			"\1\61\1\uffff\1\61\5\uffff\1\61\16\uffff\1\61\7\uffff\1\61\2\uffff\1"+
			"\61\2\uffff\1\61\43\uffff\1\61\31\uffff\1\60\1\61\30\uffff\1\57",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"\1\62",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"\1\52\7\uffff\1\52\26\uffff\1\53",
			"",
			"",
			"\1\56\47\uffff\1\55\7\uffff\1\55",
			"",
			"",
			"",
			"",
			"",
			"\1\30\55\uffff\1\27"
	};

	static final short[] DFA1_eot = DFA.unpackEncodedString(DFA1_eotS);
	static final short[] DFA1_eof = DFA.unpackEncodedString(DFA1_eofS);
	static final char[] DFA1_min = DFA.unpackEncodedStringToUnsignedChars(DFA1_minS);
	static final char[] DFA1_max = DFA.unpackEncodedStringToUnsignedChars(DFA1_maxS);
	static final short[] DFA1_accept = DFA.unpackEncodedString(DFA1_acceptS);
	static final short[] DFA1_special = DFA.unpackEncodedString(DFA1_specialS);
	static final short[][] DFA1_transition;

	static {
		int numStates = DFA1_transitionS.length;
		DFA1_transition = new short[numStates][];
		for (int i=0; i<numStates; i++) {
			DFA1_transition[i] = DFA.unpackEncodedString(DFA1_transitionS[i]);
		}
	}

	protected class DFA1 extends DFA {

		public DFA1(BaseRecognizer recognizer) {
			this.recognizer = recognizer;
			this.decisionNumber = 1;
			this.eot = DFA1_eot;
			this.eof = DFA1_eof;
			this.min = DFA1_min;
			this.max = DFA1_max;
			this.accept = DFA1_accept;
			this.special = DFA1_special;
			this.transition = DFA1_transition;
		}
		@Override
		public String getDescription() {
			return "207:1: cqlStatement returns [CQLStatement.Raw stmt] : (st1= selectStatement |st2= insertStatement |st3= updateStatement |st4= batchStatement |st5= deleteStatement |st6= useStatement |st7= truncateStatement |st8= createKeyspaceStatement |st9= createTableStatement |st10= createIndexStatement |st11= dropKeyspaceStatement |st12= dropTableStatement |st13= dropIndexStatement |st14= alterTableStatement |st15= alterKeyspaceStatement |st16= grantPermissionsStatement |st17= revokePermissionsStatement |st18= listPermissionsStatement |st19= createUserStatement |st20= alterUserStatement |st21= dropUserStatement |st22= listUsersStatement |st23= createTriggerStatement |st24= dropTriggerStatement |st25= createTypeStatement |st26= alterTypeStatement |st27= dropTypeStatement |st28= createFunctionStatement |st29= dropFunctionStatement |st30= createAggregateStatement |st31= dropAggregateStatement |st32= createRoleStatement |st33= alterRoleStatement |st34= dropRoleStatement |st35= listRolesStatement |st36= grantRoleStatement |st37= revokeRoleStatement |st38= createMaterializedViewStatement |st39= dropMaterializedViewStatement |st40= alterMaterializedViewStatement );";
		}
	}

	static final String DFA2_eotS =
		"\64\uffff";
	static final String DFA2_eofS =
		"\64\uffff";
	static final String DFA2_minS =
		"\1\6\1\0\62\uffff";
	static final String DFA2_maxS =
		"\1\u00d2\1\0\62\uffff";
	static final String DFA2_acceptS =
		"\2\uffff\1\2\60\uffff\1\1";
	static final String DFA2_specialS =
		"\1\uffff\1\0\62\uffff}>";
	static final String[] DFA2_transitionS = {
			"\1\2\4\uffff\1\2\5\uffff\1\2\3\uffff\1\2\1\uffff\2\2\4\uffff\2\2\4\uffff"+
			"\1\2\1\uffff\1\2\3\uffff\3\2\1\uffff\3\2\1\uffff\4\2\1\uffff\1\2\1\uffff"+
			"\2\2\4\uffff\2\2\1\uffff\1\2\2\uffff\4\2\1\uffff\1\2\1\uffff\2\2\1\uffff"+
			"\1\2\3\uffff\3\2\1\uffff\1\2\2\uffff\1\1\2\2\1\uffff\3\2\1\uffff\3\2"+
			"\4\uffff\3\2\1\uffff\1\2\1\uffff\1\2\2\uffff\1\2\2\uffff\7\2\3\uffff"+
			"\1\2\1\uffff\2\2\2\uffff\13\2\1\uffff\2\2\1\uffff\3\2\4\uffff\2\2\1\uffff"+
			"\4\2\3\uffff\1\2\10\uffff\2\2\3\uffff\1\2\2\uffff\1\2\10\uffff\1\2\4"+
			"\uffff\1\2\3\uffff\1\2\6\uffff\2\2\2\uffff\1\2",
			"\1\uffff",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			""
	};

	static final short[] DFA2_eot = DFA.unpackEncodedString(DFA2_eotS);
	static final short[] DFA2_eof = DFA.unpackEncodedString(DFA2_eofS);
	static final char[] DFA2_min = DFA.unpackEncodedStringToUnsignedChars(DFA2_minS);
	static final char[] DFA2_max = DFA.unpackEncodedStringToUnsignedChars(DFA2_maxS);
	static final short[] DFA2_accept = DFA.unpackEncodedString(DFA2_acceptS);
	static final short[] DFA2_special = DFA.unpackEncodedString(DFA2_specialS);
	static final short[][] DFA2_transition;

	static {
		int numStates = DFA2_transitionS.length;
		DFA2_transition = new short[numStates][];
		for (int i=0; i<numStates; i++) {
			DFA2_transition[i] = DFA.unpackEncodedString(DFA2_transitionS[i]);
		}
	}

	protected class DFA2 extends DFA {

		public DFA2(BaseRecognizer recognizer) {
			this.recognizer = recognizer;
			this.decisionNumber = 2;
			this.eot = DFA2_eot;
			this.eof = DFA2_eof;
			this.min = DFA2_min;
			this.max = DFA2_max;
			this.accept = DFA2_accept;
			this.special = DFA2_special;
			this.transition = DFA2_transition;
		}
		@Override
		public String getDescription() {
			return "275:7: ( ( K_JSON selectClause )=> K_JSON )?";
		}
		@Override
		public int specialStateTransition(int s, IntStream _input) throws NoViableAltException {
			TokenStream input = (TokenStream)_input;
			int _s = s;
			switch ( s ) {
					case 0 : 
						int LA2_1 = input.LA(1);
						 
						int index2_1 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred1_Parser()) ) {s = 51;}
						else if ( (true) ) {s = 2;}
						 
						input.seek(index2_1);
						if ( s>=0 ) return s;
						break;
			}
			if (state.backtracking>0) {state.failed=true; return -1;}
			NoViableAltException nvae =
				new NoViableAltException(getDescription(), 2, _s, input);
			error(nvae);
			throw nvae;
		}
	}

	static final String DFA11_eotS =
		"\63\uffff";
	static final String DFA11_eofS =
		"\63\uffff";
	static final String DFA11_minS =
		"\1\6\1\0\61\uffff";
	static final String DFA11_maxS =
		"\1\u00d2\1\0\61\uffff";
	static final String DFA11_acceptS =
		"\2\uffff\1\2\57\uffff\1\1";
	static final String DFA11_specialS =
		"\1\uffff\1\0\61\uffff}>";
	static final String[] DFA11_transitionS = {
			"\1\2\4\uffff\1\2\5\uffff\1\2\3\uffff\1\2\1\uffff\2\2\4\uffff\2\2\4\uffff"+
			"\1\2\1\uffff\1\2\3\uffff\3\2\1\uffff\3\2\1\uffff\4\2\1\uffff\1\2\1\uffff"+
			"\2\2\4\uffff\1\1\1\2\1\uffff\1\2\2\uffff\4\2\1\uffff\1\2\1\uffff\2\2"+
			"\1\uffff\1\2\3\uffff\3\2\1\uffff\1\2\2\uffff\3\2\1\uffff\3\2\1\uffff"+
			"\3\2\4\uffff\3\2\1\uffff\1\2\1\uffff\1\2\2\uffff\1\2\2\uffff\7\2\3\uffff"+
			"\1\2\1\uffff\2\2\2\uffff\13\2\1\uffff\2\2\1\uffff\3\2\4\uffff\2\2\1\uffff"+
			"\4\2\3\uffff\1\2\10\uffff\2\2\3\uffff\1\2\2\uffff\1\2\10\uffff\1\2\4"+
			"\uffff\1\2\3\uffff\1\2\6\uffff\2\2\2\uffff\1\2",
			"\1\uffff",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			""
	};

	static final short[] DFA11_eot = DFA.unpackEncodedString(DFA11_eotS);
	static final short[] DFA11_eof = DFA.unpackEncodedString(DFA11_eofS);
	static final char[] DFA11_min = DFA.unpackEncodedStringToUnsignedChars(DFA11_minS);
	static final char[] DFA11_max = DFA.unpackEncodedStringToUnsignedChars(DFA11_maxS);
	static final short[] DFA11_accept = DFA.unpackEncodedString(DFA11_acceptS);
	static final short[] DFA11_special = DFA.unpackEncodedString(DFA11_specialS);
	static final short[][] DFA11_transition;

	static {
		int numStates = DFA11_transitionS.length;
		DFA11_transition = new short[numStates][];
		for (int i=0; i<numStates; i++) {
			DFA11_transition[i] = DFA.unpackEncodedString(DFA11_transitionS[i]);
		}
	}

	protected class DFA11 extends DFA {

		public DFA11(BaseRecognizer recognizer) {
			this.recognizer = recognizer;
			this.decisionNumber = 11;
			this.eot = DFA11_eot;
			this.eof = DFA11_eof;
			this.min = DFA11_min;
			this.max = DFA11_max;
			this.accept = DFA11_accept;
			this.special = DFA11_special;
			this.transition = DFA11_transition;
		}
		@Override
		public String getDescription() {
			return "294:1: selectClause returns [boolean isDistinct, List<RawSelector> selectors] : ( ( K_DISTINCT selectors )=> K_DISTINCT s= selectors |s= selectors );";
		}
		@Override
		public int specialStateTransition(int s, IntStream _input) throws NoViableAltException {
			TokenStream input = (TokenStream)_input;
			int _s = s;
			switch ( s ) {
					case 0 : 
						int LA11_1 = input.LA(1);
						 
						int index11_1 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred2_Parser()) ) {s = 50;}
						else if ( (true) ) {s = 2;}
						 
						input.seek(index11_1);
						if ( s>=0 ) return s;
						break;
			}
			if (state.backtracking>0) {state.failed=true; return -1;}
			NoViableAltException nvae =
				new NoViableAltException(getDescription(), 11, _s, input);
			error(nvae);
			throw nvae;
		}
	}

	static final String DFA17_eotS =
		"\62\uffff";
	static final String DFA17_eofS =
		"\62\uffff";
	static final String DFA17_minS =
		"\1\6\56\0\3\uffff";
	static final String DFA17_maxS =
		"\1\u00d2\56\0\3\uffff";
	static final String DFA17_acceptS =
		"\57\uffff\1\3\1\1\1\2";
	static final String DFA17_specialS =
		"\1\uffff\1\0\1\1\1\2\1\3\1\4\1\5\1\6\1\7\1\10\1\11\1\12\1\13\1\14\1\15"+
		"\1\16\1\17\1\20\1\21\1\22\1\23\1\24\1\25\1\26\1\27\1\30\1\31\1\32\1\33"+
		"\1\34\1\35\1\36\1\37\1\40\1\41\1\42\1\43\1\44\1\45\1\46\1\47\1\50\1\51"+
		"\1\52\1\53\1\54\1\55\3\uffff}>";
	static final String[] DFA17_transitionS = {
			"\1\35\4\uffff\1\36\5\uffff\1\34\3\uffff\1\40\1\uffff\1\1\1\33\4\uffff"+
			"\2\3\4\uffff\1\3\1\uffff\1\4\3\uffff\1\5\1\6\1\7\1\uffff\1\3\1\51\1\3"+
			"\1\uffff\2\3\1\31\1\10\1\uffff\1\3\1\uffff\1\27\1\11\4\uffff\1\52\1\12"+
			"\1\uffff\1\13\2\uffff\3\3\1\14\1\uffff\1\3\1\uffff\2\3\1\uffff\1\3\3"+
			"\uffff\1\15\2\3\1\uffff\1\16\2\uffff\2\52\1\3\1\uffff\3\3\1\uffff\3\3"+
			"\4\uffff\1\43\1\41\1\3\1\uffff\1\3\1\uffff\1\44\2\uffff\1\3\2\uffff\5"+
			"\3\1\42\1\41\3\uffff\1\3\1\uffff\2\3\2\uffff\1\3\1\17\4\3\1\20\1\30\1"+
			"\21\1\26\1\22\1\uffff\1\53\1\3\1\uffff\1\50\2\3\4\uffff\2\3\1\uffff\1"+
			"\23\1\3\1\24\1\25\3\uffff\1\47\10\uffff\1\46\1\2\3\uffff\1\32\2\uffff"+
			"\1\37\10\uffff\1\54\4\uffff\1\57\3\uffff\1\45\6\uffff\1\55\3\uffff\1"+
			"\56",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"",
			"",
			""
	};

	static final short[] DFA17_eot = DFA.unpackEncodedString(DFA17_eotS);
	static final short[] DFA17_eof = DFA.unpackEncodedString(DFA17_eofS);
	static final char[] DFA17_min = DFA.unpackEncodedStringToUnsignedChars(DFA17_minS);
	static final char[] DFA17_max = DFA.unpackEncodedStringToUnsignedChars(DFA17_maxS);
	static final short[] DFA17_accept = DFA.unpackEncodedString(DFA17_acceptS);
	static final short[] DFA17_special = DFA.unpackEncodedString(DFA17_specialS);
	static final short[][] DFA17_transition;

	static {
		int numStates = DFA17_transitionS.length;
		DFA17_transition = new short[numStates][];
		for (int i=0; i<numStates; i++) {
			DFA17_transition[i] = DFA.unpackEncodedString(DFA17_transitionS[i]);
		}
	}

	protected class DFA17 extends DFA {

		public DFA17(BaseRecognizer recognizer) {
			this.recognizer = recognizer;
			this.decisionNumber = 17;
			this.eot = DFA17_eot;
			this.eof = DFA17_eof;
			this.min = DFA17_min;
			this.max = DFA17_max;
			this.accept = DFA17_accept;
			this.special = DFA17_special;
			this.transition = DFA17_transition;
		}
		@Override
		public String getDescription() {
			return "330:1: selectionGroup returns [Selectable.Raw s] : ( ( selectionGroupWithField )=>f= selectionGroupWithField |g= selectionGroupWithoutField | '-' g= selectionGroup );";
		}
		@Override
		public int specialStateTransition(int s, IntStream _input) throws NoViableAltException {
			TokenStream input = (TokenStream)_input;
			int _s = s;
			switch ( s ) {
					case 0 : 
						int LA17_1 = input.LA(1);
						 
						int index17_1 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred3_Parser()) ) {s = 48;}
						else if ( (true) ) {s = 49;}
						 
						input.seek(index17_1);
						if ( s>=0 ) return s;
						break;

					case 1 : 
						int LA17_2 = input.LA(1);
						 
						int index17_2 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred3_Parser()) ) {s = 48;}
						else if ( (true) ) {s = 49;}
						 
						input.seek(index17_2);
						if ( s>=0 ) return s;
						break;

					case 2 : 
						int LA17_3 = input.LA(1);
						 
						int index17_3 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred3_Parser()) ) {s = 48;}
						else if ( (true) ) {s = 49;}
						 
						input.seek(index17_3);
						if ( s>=0 ) return s;
						break;

					case 3 : 
						int LA17_4 = input.LA(1);
						 
						int index17_4 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred3_Parser()) ) {s = 48;}
						else if ( (true) ) {s = 49;}
						 
						input.seek(index17_4);
						if ( s>=0 ) return s;
						break;

					case 4 : 
						int LA17_5 = input.LA(1);
						 
						int index17_5 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred3_Parser()) ) {s = 48;}
						else if ( (true) ) {s = 49;}
						 
						input.seek(index17_5);
						if ( s>=0 ) return s;
						break;

					case 5 : 
						int LA17_6 = input.LA(1);
						 
						int index17_6 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred3_Parser()) ) {s = 48;}
						else if ( (true) ) {s = 49;}
						 
						input.seek(index17_6);
						if ( s>=0 ) return s;
						break;

					case 6 : 
						int LA17_7 = input.LA(1);
						 
						int index17_7 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred3_Parser()) ) {s = 48;}
						else if ( (true) ) {s = 49;}
						 
						input.seek(index17_7);
						if ( s>=0 ) return s;
						break;

					case 7 : 
						int LA17_8 = input.LA(1);
						 
						int index17_8 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred3_Parser()) ) {s = 48;}
						else if ( (true) ) {s = 49;}
						 
						input.seek(index17_8);
						if ( s>=0 ) return s;
						break;

					case 8 : 
						int LA17_9 = input.LA(1);
						 
						int index17_9 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred3_Parser()) ) {s = 48;}
						else if ( (true) ) {s = 49;}
						 
						input.seek(index17_9);
						if ( s>=0 ) return s;
						break;

					case 9 : 
						int LA17_10 = input.LA(1);
						 
						int index17_10 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred3_Parser()) ) {s = 48;}
						else if ( (true) ) {s = 49;}
						 
						input.seek(index17_10);
						if ( s>=0 ) return s;
						break;

					case 10 : 
						int LA17_11 = input.LA(1);
						 
						int index17_11 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred3_Parser()) ) {s = 48;}
						else if ( (true) ) {s = 49;}
						 
						input.seek(index17_11);
						if ( s>=0 ) return s;
						break;

					case 11 : 
						int LA17_12 = input.LA(1);
						 
						int index17_12 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred3_Parser()) ) {s = 48;}
						else if ( (true) ) {s = 49;}
						 
						input.seek(index17_12);
						if ( s>=0 ) return s;
						break;

					case 12 : 
						int LA17_13 = input.LA(1);
						 
						int index17_13 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred3_Parser()) ) {s = 48;}
						else if ( (true) ) {s = 49;}
						 
						input.seek(index17_13);
						if ( s>=0 ) return s;
						break;

					case 13 : 
						int LA17_14 = input.LA(1);
						 
						int index17_14 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred3_Parser()) ) {s = 48;}
						else if ( (true) ) {s = 49;}
						 
						input.seek(index17_14);
						if ( s>=0 ) return s;
						break;

					case 14 : 
						int LA17_15 = input.LA(1);
						 
						int index17_15 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred3_Parser()) ) {s = 48;}
						else if ( (true) ) {s = 49;}
						 
						input.seek(index17_15);
						if ( s>=0 ) return s;
						break;

					case 15 : 
						int LA17_16 = input.LA(1);
						 
						int index17_16 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred3_Parser()) ) {s = 48;}
						else if ( (true) ) {s = 49;}
						 
						input.seek(index17_16);
						if ( s>=0 ) return s;
						break;

					case 16 : 
						int LA17_17 = input.LA(1);
						 
						int index17_17 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred3_Parser()) ) {s = 48;}
						else if ( (true) ) {s = 49;}
						 
						input.seek(index17_17);
						if ( s>=0 ) return s;
						break;

					case 17 : 
						int LA17_18 = input.LA(1);
						 
						int index17_18 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred3_Parser()) ) {s = 48;}
						else if ( (true) ) {s = 49;}
						 
						input.seek(index17_18);
						if ( s>=0 ) return s;
						break;

					case 18 : 
						int LA17_19 = input.LA(1);
						 
						int index17_19 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred3_Parser()) ) {s = 48;}
						else if ( (true) ) {s = 49;}
						 
						input.seek(index17_19);
						if ( s>=0 ) return s;
						break;

					case 19 : 
						int LA17_20 = input.LA(1);
						 
						int index17_20 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred3_Parser()) ) {s = 48;}
						else if ( (true) ) {s = 49;}
						 
						input.seek(index17_20);
						if ( s>=0 ) return s;
						break;

					case 20 : 
						int LA17_21 = input.LA(1);
						 
						int index17_21 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred3_Parser()) ) {s = 48;}
						else if ( (true) ) {s = 49;}
						 
						input.seek(index17_21);
						if ( s>=0 ) return s;
						break;

					case 21 : 
						int LA17_22 = input.LA(1);
						 
						int index17_22 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred3_Parser()) ) {s = 48;}
						else if ( (true) ) {s = 49;}
						 
						input.seek(index17_22);
						if ( s>=0 ) return s;
						break;

					case 22 : 
						int LA17_23 = input.LA(1);
						 
						int index17_23 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred3_Parser()) ) {s = 48;}
						else if ( (true) ) {s = 49;}
						 
						input.seek(index17_23);
						if ( s>=0 ) return s;
						break;

					case 23 : 
						int LA17_24 = input.LA(1);
						 
						int index17_24 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred3_Parser()) ) {s = 48;}
						else if ( (true) ) {s = 49;}
						 
						input.seek(index17_24);
						if ( s>=0 ) return s;
						break;

					case 24 : 
						int LA17_25 = input.LA(1);
						 
						int index17_25 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred3_Parser()) ) {s = 48;}
						else if ( (true) ) {s = 49;}
						 
						input.seek(index17_25);
						if ( s>=0 ) return s;
						break;

					case 25 : 
						int LA17_26 = input.LA(1);
						 
						int index17_26 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred3_Parser()) ) {s = 48;}
						else if ( (true) ) {s = 49;}
						 
						input.seek(index17_26);
						if ( s>=0 ) return s;
						break;

					case 26 : 
						int LA17_27 = input.LA(1);
						 
						int index17_27 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred3_Parser()) ) {s = 48;}
						else if ( (true) ) {s = 49;}
						 
						input.seek(index17_27);
						if ( s>=0 ) return s;
						break;

					case 27 : 
						int LA17_28 = input.LA(1);
						 
						int index17_28 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred3_Parser()) ) {s = 48;}
						else if ( (true) ) {s = 49;}
						 
						input.seek(index17_28);
						if ( s>=0 ) return s;
						break;

					case 28 : 
						int LA17_29 = input.LA(1);
						 
						int index17_29 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred3_Parser()) ) {s = 48;}
						else if ( (true) ) {s = 49;}
						 
						input.seek(index17_29);
						if ( s>=0 ) return s;
						break;

					case 29 : 
						int LA17_30 = input.LA(1);
						 
						int index17_30 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred3_Parser()) ) {s = 48;}
						else if ( (true) ) {s = 49;}
						 
						input.seek(index17_30);
						if ( s>=0 ) return s;
						break;

					case 30 : 
						int LA17_31 = input.LA(1);
						 
						int index17_31 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred3_Parser()) ) {s = 48;}
						else if ( (true) ) {s = 49;}
						 
						input.seek(index17_31);
						if ( s>=0 ) return s;
						break;

					case 31 : 
						int LA17_32 = input.LA(1);
						 
						int index17_32 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred3_Parser()) ) {s = 48;}
						else if ( (true) ) {s = 49;}
						 
						input.seek(index17_32);
						if ( s>=0 ) return s;
						break;

					case 32 : 
						int LA17_33 = input.LA(1);
						 
						int index17_33 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred3_Parser()) ) {s = 48;}
						else if ( (true) ) {s = 49;}
						 
						input.seek(index17_33);
						if ( s>=0 ) return s;
						break;

					case 33 : 
						int LA17_34 = input.LA(1);
						 
						int index17_34 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred3_Parser()) ) {s = 48;}
						else if ( (true) ) {s = 49;}
						 
						input.seek(index17_34);
						if ( s>=0 ) return s;
						break;

					case 34 : 
						int LA17_35 = input.LA(1);
						 
						int index17_35 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred3_Parser()) ) {s = 48;}
						else if ( (true) ) {s = 49;}
						 
						input.seek(index17_35);
						if ( s>=0 ) return s;
						break;

					case 35 : 
						int LA17_36 = input.LA(1);
						 
						int index17_36 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred3_Parser()) ) {s = 48;}
						else if ( (true) ) {s = 49;}
						 
						input.seek(index17_36);
						if ( s>=0 ) return s;
						break;

					case 36 : 
						int LA17_37 = input.LA(1);
						 
						int index17_37 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred3_Parser()) ) {s = 48;}
						else if ( (true) ) {s = 49;}
						 
						input.seek(index17_37);
						if ( s>=0 ) return s;
						break;

					case 37 : 
						int LA17_38 = input.LA(1);
						 
						int index17_38 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred3_Parser()) ) {s = 48;}
						else if ( (true) ) {s = 49;}
						 
						input.seek(index17_38);
						if ( s>=0 ) return s;
						break;

					case 38 : 
						int LA17_39 = input.LA(1);
						 
						int index17_39 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred3_Parser()) ) {s = 48;}
						else if ( (true) ) {s = 49;}
						 
						input.seek(index17_39);
						if ( s>=0 ) return s;
						break;

					case 39 : 
						int LA17_40 = input.LA(1);
						 
						int index17_40 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred3_Parser()) ) {s = 48;}
						else if ( (true) ) {s = 49;}
						 
						input.seek(index17_40);
						if ( s>=0 ) return s;
						break;

					case 40 : 
						int LA17_41 = input.LA(1);
						 
						int index17_41 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred3_Parser()) ) {s = 48;}
						else if ( (true) ) {s = 49;}
						 
						input.seek(index17_41);
						if ( s>=0 ) return s;
						break;

					case 41 : 
						int LA17_42 = input.LA(1);
						 
						int index17_42 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred3_Parser()) ) {s = 48;}
						else if ( (true) ) {s = 49;}
						 
						input.seek(index17_42);
						if ( s>=0 ) return s;
						break;

					case 42 : 
						int LA17_43 = input.LA(1);
						 
						int index17_43 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred3_Parser()) ) {s = 48;}
						else if ( (true) ) {s = 49;}
						 
						input.seek(index17_43);
						if ( s>=0 ) return s;
						break;

					case 43 : 
						int LA17_44 = input.LA(1);
						 
						int index17_44 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred3_Parser()) ) {s = 48;}
						else if ( (true) ) {s = 49;}
						 
						input.seek(index17_44);
						if ( s>=0 ) return s;
						break;

					case 44 : 
						int LA17_45 = input.LA(1);
						 
						int index17_45 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred3_Parser()) ) {s = 48;}
						else if ( (true) ) {s = 49;}
						 
						input.seek(index17_45);
						if ( s>=0 ) return s;
						break;

					case 45 : 
						int LA17_46 = input.LA(1);
						 
						int index17_46 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred3_Parser()) ) {s = 48;}
						else if ( (true) ) {s = 49;}
						 
						input.seek(index17_46);
						if ( s>=0 ) return s;
						break;
			}
			if (state.backtracking>0) {state.failed=true; return -1;}
			NoViableAltException nvae =
				new NoViableAltException(getDescription(), 17, _s, input);
			error(nvae);
			throw nvae;
		}
	}

	static final String DFA22_eotS =
		"\61\uffff";
	static final String DFA22_eofS =
		"\61\uffff";
	static final String DFA22_minS =
		"\1\6\53\uffff\1\0\4\uffff";
	static final String DFA22_maxS =
		"\1\u00d2\53\uffff\1\0\4\uffff";
	static final String DFA22_acceptS =
		"\1\uffff\1\1\53\uffff\1\4\1\5\1\2\1\3";
	static final String DFA22_specialS =
		"\54\uffff\1\0\4\uffff}>";
	static final String[] DFA22_transitionS = {
			"\1\1\4\uffff\1\1\5\uffff\1\1\3\uffff\1\1\1\uffff\2\1\4\uffff\2\1\4\uffff"+
			"\1\1\1\uffff\1\1\3\uffff\3\1\1\uffff\3\1\1\uffff\4\1\1\uffff\1\1\1\uffff"+
			"\2\1\4\uffff\2\1\1\uffff\1\1\2\uffff\4\1\1\uffff\1\1\1\uffff\2\1\1\uffff"+
			"\1\1\3\uffff\3\1\1\uffff\1\1\2\uffff\3\1\1\uffff\3\1\1\uffff\3\1\4\uffff"+
			"\3\1\1\uffff\1\1\1\uffff\1\1\2\uffff\1\1\2\uffff\7\1\3\uffff\1\1\1\uffff"+
			"\2\1\2\uffff\13\1\1\uffff\2\1\1\uffff\3\1\4\uffff\2\1\1\uffff\4\1\3\uffff"+
			"\1\1\10\uffff\2\1\3\uffff\1\1\2\uffff\1\1\10\uffff\1\54\10\uffff\1\1"+
			"\6\uffff\1\55\3\uffff\1\56",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"\1\uffff",
			"",
			"",
			"",
			""
	};

	static final short[] DFA22_eot = DFA.unpackEncodedString(DFA22_eotS);
	static final short[] DFA22_eof = DFA.unpackEncodedString(DFA22_eofS);
	static final char[] DFA22_min = DFA.unpackEncodedStringToUnsignedChars(DFA22_minS);
	static final char[] DFA22_max = DFA.unpackEncodedStringToUnsignedChars(DFA22_maxS);
	static final short[] DFA22_accept = DFA.unpackEncodedString(DFA22_acceptS);
	static final short[] DFA22_special = DFA.unpackEncodedString(DFA22_specialS);
	static final short[][] DFA22_transition;

	static {
		int numStates = DFA22_transitionS.length;
		DFA22_transition = new short[numStates][];
		for (int i=0; i<numStates; i++) {
			DFA22_transition[i] = DFA.unpackEncodedString(DFA22_transitionS[i]);
		}
	}

	protected class DFA22 extends DFA {

		public DFA22(BaseRecognizer recognizer) {
			this.recognizer = recognizer;
			this.decisionNumber = 22;
			this.eot = DFA22_eot;
			this.eof = DFA22_eof;
			this.min = DFA22_min;
			this.max = DFA22_max;
			this.accept = DFA22_accept;
			this.special = DFA22_special;
			this.transition = DFA22_transition;
		}
		@Override
		public String getDescription() {
			return "361:1: selectionGroupWithoutField returns [Selectable.Raw s] : (sn= simpleUnaliasedSelector | ( selectionTypeHint )=>h= selectionTypeHint |t= selectionTupleOrNestedSelector |l= selectionList |m= selectionMapOrSet );";
		}
		@Override
		public int specialStateTransition(int s, IntStream _input) throws NoViableAltException {
			TokenStream input = (TokenStream)_input;
			int _s = s;
			switch ( s ) {
					case 0 : 
						int LA22_44 = input.LA(1);
						 
						int index22_44 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred4_Parser()) ) {s = 47;}
						else if ( (true) ) {s = 48;}
						 
						input.seek(index22_44);
						if ( s>=0 ) return s;
						break;
			}
			if (state.backtracking>0) {state.failed=true; return -1;}
			NoViableAltException nvae =
				new NoViableAltException(getDescription(), 22, _s, input);
			error(nvae);
			throw nvae;
		}
	}

	static final String DFA30_eotS =
		"\126\uffff";
	static final String DFA30_eofS =
		"\1\uffff\31\41\1\uffff\1\32\4\41\4\uffff\31\41\31\32";
	static final String DFA30_minS =
		"\1\6\31\43\1\uffff\5\43\2\uffff\2\27\62\43";
	static final String DFA30_maxS =
		"\1\u00c7\31\u00d3\1\uffff\5\u00d3\2\uffff\2\u00ae\62\u00d3";
	static final String DFA30_acceptS =
		"\32\uffff\1\2\5\uffff\1\3\1\1\64\uffff";
	static final String DFA30_specialS =
		"\126\uffff}>";
	static final String[] DFA30_transitionS = {
			"\1\32\4\uffff\1\32\5\uffff\1\32\3\uffff\1\32\1\uffff\1\1\1\32\4\uffff"+
			"\2\3\4\uffff\1\3\1\uffff\1\4\3\uffff\1\5\1\6\1\7\1\uffff\1\3\1\36\1\3"+
			"\1\uffff\2\3\1\31\1\10\1\uffff\1\3\1\uffff\1\27\1\11\4\uffff\1\37\1\12"+
			"\1\uffff\1\13\2\uffff\3\3\1\14\1\uffff\1\3\1\uffff\2\3\1\uffff\1\3\3"+
			"\uffff\1\15\2\3\1\uffff\1\16\2\uffff\2\37\1\3\1\uffff\3\3\1\uffff\3\3"+
			"\4\uffff\2\32\1\3\1\uffff\1\3\1\uffff\1\32\2\uffff\1\3\2\uffff\5\3\2"+
			"\32\3\uffff\1\3\1\uffff\2\3\2\uffff\1\3\1\17\4\3\1\20\1\30\1\21\1\26"+
			"\1\22\1\uffff\1\40\1\3\1\uffff\1\35\2\3\4\uffff\2\3\1\uffff\1\23\1\3"+
			"\1\24\1\25\3\uffff\1\34\10\uffff\1\33\1\2\3\uffff\1\32\2\uffff\1\32\21"+
			"\uffff\1\32",
			"\1\41\44\uffff\1\41\164\uffff\1\41\1\40\2\41\1\uffff\2\41\1\uffff\1"+
			"\42\2\41\6\uffff\3\41\2\uffff\1\41",
			"\1\41\44\uffff\1\41\164\uffff\1\41\1\40\2\41\1\uffff\2\41\1\uffff\1"+
			"\42\2\41\6\uffff\3\41\2\uffff\1\41",
			"\1\41\44\uffff\1\41\164\uffff\1\41\1\40\2\41\1\uffff\2\41\1\uffff\1"+
			"\42\2\41\6\uffff\3\41\2\uffff\1\41",
			"\1\41\44\uffff\1\41\164\uffff\1\41\1\40\2\41\1\uffff\2\41\1\uffff\1"+
			"\42\2\41\6\uffff\3\41\2\uffff\1\41",
			"\1\41\44\uffff\1\41\164\uffff\1\41\1\40\2\41\1\uffff\2\41\1\uffff\1"+
			"\42\2\41\6\uffff\3\41\2\uffff\1\41",
			"\1\41\44\uffff\1\41\164\uffff\1\41\1\40\2\41\1\uffff\2\41\1\uffff\1"+
			"\42\2\41\6\uffff\3\41\2\uffff\1\41",
			"\1\41\44\uffff\1\41\164\uffff\1\41\1\40\2\41\1\uffff\2\41\1\uffff\1"+
			"\42\2\41\6\uffff\3\41\2\uffff\1\41",
			"\1\41\44\uffff\1\41\164\uffff\1\41\1\40\2\41\1\uffff\2\41\1\uffff\1"+
			"\42\2\41\6\uffff\3\41\2\uffff\1\41",
			"\1\41\44\uffff\1\41\164\uffff\1\41\1\40\2\41\1\uffff\2\41\1\uffff\1"+
			"\42\2\41\6\uffff\3\41\2\uffff\1\41",
			"\1\41\44\uffff\1\41\164\uffff\1\41\1\40\2\41\1\uffff\2\41\1\uffff\1"+
			"\42\2\41\6\uffff\3\41\2\uffff\1\41",
			"\1\41\44\uffff\1\41\164\uffff\1\41\1\40\2\41\1\uffff\2\41\1\uffff\1"+
			"\42\2\41\6\uffff\3\41\2\uffff\1\41",
			"\1\41\44\uffff\1\41\164\uffff\1\41\1\40\2\41\1\uffff\2\41\1\uffff\1"+
			"\42\2\41\6\uffff\3\41\2\uffff\1\41",
			"\1\41\44\uffff\1\41\164\uffff\1\41\1\40\2\41\1\uffff\2\41\1\uffff\1"+
			"\42\2\41\6\uffff\3\41\2\uffff\1\41",
			"\1\41\44\uffff\1\41\164\uffff\1\41\1\40\2\41\1\uffff\2\41\1\uffff\1"+
			"\42\2\41\6\uffff\3\41\2\uffff\1\41",
			"\1\41\44\uffff\1\41\164\uffff\1\41\1\40\2\41\1\uffff\2\41\1\uffff\1"+
			"\42\2\41\6\uffff\3\41\2\uffff\1\41",
			"\1\41\44\uffff\1\41\164\uffff\1\41\1\40\2\41\1\uffff\2\41\1\uffff\1"+
			"\42\2\41\6\uffff\3\41\2\uffff\1\41",
			"\1\41\44\uffff\1\41\164\uffff\1\41\1\40\2\41\1\uffff\2\41\1\uffff\1"+
			"\42\2\41\6\uffff\3\41\2\uffff\1\41",
			"\1\41\44\uffff\1\41\164\uffff\1\41\1\40\2\41\1\uffff\2\41\1\uffff\1"+
			"\42\2\41\6\uffff\3\41\2\uffff\1\41",
			"\1\41\44\uffff\1\41\164\uffff\1\41\1\40\2\41\1\uffff\2\41\1\uffff\1"+
			"\42\2\41\6\uffff\3\41\2\uffff\1\41",
			"\1\41\44\uffff\1\41\164\uffff\1\41\1\40\2\41\1\uffff\2\41\1\uffff\1"+
			"\42\2\41\6\uffff\3\41\2\uffff\1\41",
			"\1\41\44\uffff\1\41\164\uffff\1\41\1\40\2\41\1\uffff\2\41\1\uffff\1"+
			"\42\2\41\6\uffff\3\41\2\uffff\1\41",
			"\1\41\44\uffff\1\41\164\uffff\1\41\1\40\2\41\1\uffff\2\41\1\uffff\1"+
			"\42\2\41\6\uffff\3\41\2\uffff\1\41",
			"\1\41\44\uffff\1\41\164\uffff\1\41\1\40\2\41\1\uffff\2\41\1\uffff\1"+
			"\42\2\41\6\uffff\3\41\2\uffff\1\41",
			"\1\41\44\uffff\1\41\164\uffff\1\41\1\40\2\41\1\uffff\2\41\1\uffff\1"+
			"\42\2\41\6\uffff\3\41\2\uffff\1\41",
			"\1\41\44\uffff\1\41\164\uffff\1\41\1\40\2\41\1\uffff\2\41\1\uffff\1"+
			"\42\2\41\6\uffff\3\41\2\uffff\1\41",
			"",
			"\1\32\44\uffff\1\32\164\uffff\1\32\1\uffff\2\32\1\uffff\2\32\1\uffff"+
			"\1\43\2\32\6\uffff\3\32\2\uffff\1\32",
			"\1\41\44\uffff\1\41\164\uffff\1\41\1\40\2\41\1\uffff\2\41\1\uffff\1"+
			"\42\2\41\6\uffff\3\41\2\uffff\1\41",
			"\1\41\44\uffff\1\41\164\uffff\1\41\1\40\2\41\1\uffff\2\41\1\uffff\1"+
			"\42\2\41\6\uffff\3\41\2\uffff\1\41",
			"\1\41\44\uffff\1\41\164\uffff\1\41\1\40\2\41\1\uffff\2\41\1\uffff\1"+
			"\42\2\41\6\uffff\3\41\2\uffff\1\41",
			"\1\41\44\uffff\1\41\164\uffff\1\41\1\uffff\2\41\1\uffff\2\41\1\uffff"+
			"\1\42\2\41\6\uffff\3\41\2\uffff\1\41",
			"",
			"",
			"\1\44\5\uffff\2\46\4\uffff\1\46\1\uffff\1\47\3\uffff\1\50\1\51\1\52"+
			"\1\uffff\1\46\1\41\1\46\1\uffff\2\46\1\74\1\53\1\uffff\1\46\1\uffff\1"+
			"\72\1\54\4\uffff\1\41\1\55\1\uffff\1\56\2\uffff\3\46\1\57\1\uffff\1\46"+
			"\1\uffff\2\46\1\uffff\1\46\3\uffff\1\60\2\46\1\uffff\1\61\2\uffff\2\41"+
			"\1\46\1\uffff\3\46\1\uffff\3\46\6\uffff\1\46\1\uffff\1\46\4\uffff\1\46"+
			"\2\uffff\5\46\5\uffff\1\46\1\uffff\2\46\2\uffff\1\46\1\62\4\46\1\63\1"+
			"\73\1\64\1\71\1\65\1\uffff\1\40\1\46\1\uffff\1\41\2\46\4\uffff\2\46\1"+
			"\uffff\1\66\1\46\1\67\1\70\3\uffff\1\41\11\uffff\1\45",
			"\1\75\5\uffff\2\77\4\uffff\1\77\1\uffff\1\100\3\uffff\1\101\1\102\1"+
			"\103\1\uffff\1\77\1\32\1\77\1\uffff\2\77\1\125\1\104\1\uffff\1\77\1\uffff"+
			"\1\123\1\105\4\uffff\1\32\1\106\1\uffff\1\107\2\uffff\3\77\1\110\1\uffff"+
			"\1\77\1\uffff\2\77\1\uffff\1\77\3\uffff\1\111\2\77\1\uffff\1\112\2\uffff"+
			"\2\32\1\77\1\uffff\3\77\1\uffff\3\77\6\uffff\1\77\1\uffff\1\77\4\uffff"+
			"\1\77\2\uffff\5\77\5\uffff\1\77\1\uffff\2\77\2\uffff\1\77\1\113\4\77"+
			"\1\114\1\124\1\115\1\122\1\116\1\uffff\1\40\1\77\1\uffff\1\32\2\77\4"+
			"\uffff\2\77\1\uffff\1\117\1\77\1\120\1\121\3\uffff\1\32\11\uffff\1\76",
			"\1\41\44\uffff\1\41\164\uffff\1\41\1\40\2\41\1\uffff\2\41\1\uffff\3"+
			"\41\6\uffff\3\41\2\uffff\1\41",
			"\1\41\44\uffff\1\41\164\uffff\1\41\1\40\2\41\1\uffff\2\41\1\uffff\3"+
			"\41\6\uffff\3\41\2\uffff\1\41",
			"\1\41\44\uffff\1\41\164\uffff\1\41\1\40\2\41\1\uffff\2\41\1\uffff\3"+
			"\41\6\uffff\3\41\2\uffff\1\41",
			"\1\41\44\uffff\1\41\164\uffff\1\41\1\40\2\41\1\uffff\2\41\1\uffff\3"+
			"\41\6\uffff\3\41\2\uffff\1\41",
			"\1\41\44\uffff\1\41\164\uffff\1\41\1\40\2\41\1\uffff\2\41\1\uffff\3"+
			"\41\6\uffff\3\41\2\uffff\1\41",
			"\1\41\44\uffff\1\41\164\uffff\1\41\1\40\2\41\1\uffff\2\41\1\uffff\3"+
			"\41\6\uffff\3\41\2\uffff\1\41",
			"\1\41\44\uffff\1\41\164\uffff\1\41\1\40\2\41\1\uffff\2\41\1\uffff\3"+
			"\41\6\uffff\3\41\2\uffff\1\41",
			"\1\41\44\uffff\1\41\164\uffff\1\41\1\40\2\41\1\uffff\2\41\1\uffff\3"+
			"\41\6\uffff\3\41\2\uffff\1\41",
			"\1\41\44\uffff\1\41\164\uffff\1\41\1\40\2\41\1\uffff\2\41\1\uffff\3"+
			"\41\6\uffff\3\41\2\uffff\1\41",
			"\1\41\44\uffff\1\41\164\uffff\1\41\1\40\2\41\1\uffff\2\41\1\uffff\3"+
			"\41\6\uffff\3\41\2\uffff\1\41",
			"\1\41\44\uffff\1\41\164\uffff\1\41\1\40\2\41\1\uffff\2\41\1\uffff\3"+
			"\41\6\uffff\3\41\2\uffff\1\41",
			"\1\41\44\uffff\1\41\164\uffff\1\41\1\40\2\41\1\uffff\2\41\1\uffff\3"+
			"\41\6\uffff\3\41\2\uffff\1\41",
			"\1\41\44\uffff\1\41\164\uffff\1\41\1\40\2\41\1\uffff\2\41\1\uffff\3"+
			"\41\6\uffff\3\41\2\uffff\1\41",
			"\1\41\44\uffff\1\41\164\uffff\1\41\1\40\2\41\1\uffff\2\41\1\uffff\3"+
			"\41\6\uffff\3\41\2\uffff\1\41",
			"\1\41\44\uffff\1\41\164\uffff\1\41\1\40\2\41\1\uffff\2\41\1\uffff\3"+
			"\41\6\uffff\3\41\2\uffff\1\41",
			"\1\41\44\uffff\1\41\164\uffff\1\41\1\40\2\41\1\uffff\2\41\1\uffff\3"+
			"\41\6\uffff\3\41\2\uffff\1\41",
			"\1\41\44\uffff\1\41\164\uffff\1\41\1\40\2\41\1\uffff\2\41\1\uffff\3"+
			"\41\6\uffff\3\41\2\uffff\1\41",
			"\1\41\44\uffff\1\41\164\uffff\1\41\1\40\2\41\1\uffff\2\41\1\uffff\3"+
			"\41\6\uffff\3\41\2\uffff\1\41",
			"\1\41\44\uffff\1\41\164\uffff\1\41\1\40\2\41\1\uffff\2\41\1\uffff\3"+
			"\41\6\uffff\3\41\2\uffff\1\41",
			"\1\41\44\uffff\1\41\164\uffff\1\41\1\40\2\41\1\uffff\2\41\1\uffff\3"+
			"\41\6\uffff\3\41\2\uffff\1\41",
			"\1\41\44\uffff\1\41\164\uffff\1\41\1\40\2\41\1\uffff\2\41\1\uffff\3"+
			"\41\6\uffff\3\41\2\uffff\1\41",
			"\1\41\44\uffff\1\41\164\uffff\1\41\1\40\2\41\1\uffff\2\41\1\uffff\3"+
			"\41\6\uffff\3\41\2\uffff\1\41",
			"\1\41\44\uffff\1\41\164\uffff\1\41\1\40\2\41\1\uffff\2\41\1\uffff\3"+
			"\41\6\uffff\3\41\2\uffff\1\41",
			"\1\41\44\uffff\1\41\164\uffff\1\41\1\40\2\41\1\uffff\2\41\1\uffff\3"+
			"\41\6\uffff\3\41\2\uffff\1\41",
			"\1\41\44\uffff\1\41\164\uffff\1\41\1\40\2\41\1\uffff\2\41\1\uffff\3"+
			"\41\6\uffff\3\41\2\uffff\1\41",
			"\1\32\44\uffff\1\32\164\uffff\1\32\1\40\2\32\1\uffff\2\32\1\uffff\3"+
			"\32\6\uffff\3\32\2\uffff\1\32",
			"\1\32\44\uffff\1\32\164\uffff\1\32\1\40\2\32\1\uffff\2\32\1\uffff\3"+
			"\32\6\uffff\3\32\2\uffff\1\32",
			"\1\32\44\uffff\1\32\164\uffff\1\32\1\40\2\32\1\uffff\2\32\1\uffff\3"+
			"\32\6\uffff\3\32\2\uffff\1\32",
			"\1\32\44\uffff\1\32\164\uffff\1\32\1\40\2\32\1\uffff\2\32\1\uffff\3"+
			"\32\6\uffff\3\32\2\uffff\1\32",
			"\1\32\44\uffff\1\32\164\uffff\1\32\1\40\2\32\1\uffff\2\32\1\uffff\3"+
			"\32\6\uffff\3\32\2\uffff\1\32",
			"\1\32\44\uffff\1\32\164\uffff\1\32\1\40\2\32\1\uffff\2\32\1\uffff\3"+
			"\32\6\uffff\3\32\2\uffff\1\32",
			"\1\32\44\uffff\1\32\164\uffff\1\32\1\40\2\32\1\uffff\2\32\1\uffff\3"+
			"\32\6\uffff\3\32\2\uffff\1\32",
			"\1\32\44\uffff\1\32\164\uffff\1\32\1\40\2\32\1\uffff\2\32\1\uffff\3"+
			"\32\6\uffff\3\32\2\uffff\1\32",
			"\1\32\44\uffff\1\32\164\uffff\1\32\1\40\2\32\1\uffff\2\32\1\uffff\3"+
			"\32\6\uffff\3\32\2\uffff\1\32",
			"\1\32\44\uffff\1\32\164\uffff\1\32\1\40\2\32\1\uffff\2\32\1\uffff\3"+
			"\32\6\uffff\3\32\2\uffff\1\32",
			"\1\32\44\uffff\1\32\164\uffff\1\32\1\40\2\32\1\uffff\2\32\1\uffff\3"+
			"\32\6\uffff\3\32\2\uffff\1\32",
			"\1\32\44\uffff\1\32\164\uffff\1\32\1\40\2\32\1\uffff\2\32\1\uffff\3"+
			"\32\6\uffff\3\32\2\uffff\1\32",
			"\1\32\44\uffff\1\32\164\uffff\1\32\1\40\2\32\1\uffff\2\32\1\uffff\3"+
			"\32\6\uffff\3\32\2\uffff\1\32",
			"\1\32\44\uffff\1\32\164\uffff\1\32\1\40\2\32\1\uffff\2\32\1\uffff\3"+
			"\32\6\uffff\3\32\2\uffff\1\32",
			"\1\32\44\uffff\1\32\164\uffff\1\32\1\40\2\32\1\uffff\2\32\1\uffff\3"+
			"\32\6\uffff\3\32\2\uffff\1\32",
			"\1\32\44\uffff\1\32\164\uffff\1\32\1\40\2\32\1\uffff\2\32\1\uffff\3"+
			"\32\6\uffff\3\32\2\uffff\1\32",
			"\1\32\44\uffff\1\32\164\uffff\1\32\1\40\2\32\1\uffff\2\32\1\uffff\3"+
			"\32\6\uffff\3\32\2\uffff\1\32",
			"\1\32\44\uffff\1\32\164\uffff\1\32\1\40\2\32\1\uffff\2\32\1\uffff\3"+
			"\32\6\uffff\3\32\2\uffff\1\32",
			"\1\32\44\uffff\1\32\164\uffff\1\32\1\40\2\32\1\uffff\2\32\1\uffff\3"+
			"\32\6\uffff\3\32\2\uffff\1\32",
			"\1\32\44\uffff\1\32\164\uffff\1\32\1\40\2\32\1\uffff\2\32\1\uffff\3"+
			"\32\6\uffff\3\32\2\uffff\1\32",
			"\1\32\44\uffff\1\32\164\uffff\1\32\1\40\2\32\1\uffff\2\32\1\uffff\3"+
			"\32\6\uffff\3\32\2\uffff\1\32",
			"\1\32\44\uffff\1\32\164\uffff\1\32\1\40\2\32\1\uffff\2\32\1\uffff\3"+
			"\32\6\uffff\3\32\2\uffff\1\32",
			"\1\32\44\uffff\1\32\164\uffff\1\32\1\40\2\32\1\uffff\2\32\1\uffff\3"+
			"\32\6\uffff\3\32\2\uffff\1\32",
			"\1\32\44\uffff\1\32\164\uffff\1\32\1\40\2\32\1\uffff\2\32\1\uffff\3"+
			"\32\6\uffff\3\32\2\uffff\1\32",
			"\1\32\44\uffff\1\32\164\uffff\1\32\1\40\2\32\1\uffff\2\32\1\uffff\3"+
			"\32\6\uffff\3\32\2\uffff\1\32"
	};

	static final short[] DFA30_eot = DFA.unpackEncodedString(DFA30_eotS);
	static final short[] DFA30_eof = DFA.unpackEncodedString(DFA30_eofS);
	static final char[] DFA30_min = DFA.unpackEncodedStringToUnsignedChars(DFA30_minS);
	static final char[] DFA30_max = DFA.unpackEncodedStringToUnsignedChars(DFA30_maxS);
	static final short[] DFA30_accept = DFA.unpackEncodedString(DFA30_acceptS);
	static final short[] DFA30_special = DFA.unpackEncodedString(DFA30_specialS);
	static final short[][] DFA30_transition;

	static {
		int numStates = DFA30_transitionS.length;
		DFA30_transition = new short[numStates][];
		for (int i=0; i<numStates; i++) {
			DFA30_transition[i] = DFA.unpackEncodedString(DFA30_transitionS[i]);
		}
	}

	protected class DFA30 extends DFA {

		public DFA30(BaseRecognizer recognizer) {
			this.recognizer = recognizer;
			this.decisionNumber = 30;
			this.eot = DFA30_eot;
			this.eof = DFA30_eof;
			this.min = DFA30_min;
			this.max = DFA30_max;
			this.accept = DFA30_accept;
			this.special = DFA30_special;
			this.transition = DFA30_transition;
		}
		@Override
		public String getDescription() {
			return "409:1: simpleUnaliasedSelector returns [Selectable.Raw s] : (c= sident |l= selectionLiteral |f= selectionFunction );";
		}
	}

	static final String DFA31_eotS =
		"\13\uffff";
	static final String DFA31_eofS =
		"\13\uffff";
	static final String DFA31_minS =
		"\1\27\4\u00be\1\uffff\1\6\4\uffff";
	static final String DFA31_maxS =
		"\1\u00ae\4\u00c5\1\uffff\1\u00d2\4\uffff";
	static final String DFA31_acceptS =
		"\5\uffff\1\5\1\uffff\1\2\1\3\1\4\1\1";
	static final String DFA31_specialS =
		"\13\uffff}>";
	static final String[] DFA31_transitionS = {
			"\1\5\5\uffff\2\5\4\uffff\1\5\1\uffff\1\5\3\uffff\3\5\1\uffff\1\5\1\4"+
			"\1\5\1\uffff\2\5\1\1\1\5\1\uffff\1\5\1\uffff\2\5\4\uffff\2\5\1\uffff"+
			"\1\5\2\uffff\4\5\1\uffff\1\5\1\uffff\2\5\1\uffff\1\5\3\uffff\3\5\1\uffff"+
			"\1\5\2\uffff\3\5\1\uffff\3\5\1\uffff\3\5\6\uffff\1\5\1\uffff\1\5\4\uffff"+
			"\1\5\2\uffff\5\5\5\uffff\1\5\1\uffff\2\5\2\uffff\13\5\1\uffff\2\5\1\uffff"+
			"\1\3\2\5\4\uffff\2\5\1\uffff\4\5\3\uffff\1\2\10\uffff\2\5",
			"\1\6\6\uffff\1\5",
			"\1\7\6\uffff\1\5",
			"\1\10\6\uffff\1\5",
			"\1\11\6\uffff\1\5",
			"",
			"\1\5\4\uffff\1\5\5\uffff\1\5\3\uffff\1\5\1\uffff\2\5\4\uffff\2\5\4\uffff"+
			"\1\5\1\uffff\1\5\3\uffff\3\5\1\uffff\3\5\1\uffff\4\5\1\uffff\1\5\1\uffff"+
			"\2\5\4\uffff\2\5\1\uffff\1\5\2\uffff\4\5\1\uffff\1\5\1\uffff\2\5\1\uffff"+
			"\1\5\3\uffff\3\5\1\uffff\1\5\2\uffff\3\5\1\uffff\3\5\1\uffff\3\5\4\uffff"+
			"\3\5\1\uffff\1\5\1\uffff\1\5\2\uffff\1\5\2\uffff\7\5\3\uffff\1\5\1\uffff"+
			"\2\5\2\uffff\13\5\1\uffff\2\5\1\uffff\3\5\4\uffff\2\5\1\uffff\4\5\3\uffff"+
			"\1\5\10\uffff\2\5\3\uffff\1\5\2\uffff\1\5\10\uffff\2\5\3\uffff\1\5\3"+
			"\uffff\1\5\6\uffff\1\5\1\12\2\uffff\1\5",
			"",
			"",
			"",
			""
	};

	static final short[] DFA31_eot = DFA.unpackEncodedString(DFA31_eotS);
	static final short[] DFA31_eof = DFA.unpackEncodedString(DFA31_eofS);
	static final char[] DFA31_min = DFA.unpackEncodedStringToUnsignedChars(DFA31_minS);
	static final char[] DFA31_max = DFA.unpackEncodedStringToUnsignedChars(DFA31_maxS);
	static final short[] DFA31_accept = DFA.unpackEncodedString(DFA31_acceptS);
	static final short[] DFA31_special = DFA.unpackEncodedString(DFA31_specialS);
	static final short[][] DFA31_transition;

	static {
		int numStates = DFA31_transitionS.length;
		DFA31_transition = new short[numStates][];
		for (int i=0; i<numStates; i++) {
			DFA31_transition[i] = DFA.unpackEncodedString(DFA31_transitionS[i]);
		}
	}

	protected class DFA31 extends DFA {

		public DFA31(BaseRecognizer recognizer) {
			this.recognizer = recognizer;
			this.decisionNumber = 31;
			this.eot = DFA31_eot;
			this.eof = DFA31_eof;
			this.min = DFA31_min;
			this.max = DFA31_max;
			this.accept = DFA31_accept;
			this.special = DFA31_special;
			this.transition = DFA31_transition;
		}
		@Override
		public String getDescription() {
			return "415:1: selectionFunction returns [Selectable.Raw s] : ( K_COUNT '(' '\\*' ')' | K_WRITETIME '(' c= cident ')' | K_TTL '(' c= cident ')' | K_CAST '(' sn= unaliasedSelector K_AS t= native_type ')' |f= functionName args= selectionFunctionArgs );";
		}
	}

	static final String DFA61_eotS =
		"\36\uffff";
	static final String DFA61_eofS =
		"\36\uffff";
	static final String DFA61_minS =
		"\1\16\32\110\3\uffff";
	static final String DFA61_maxS =
		"\1\u00ae\32\u00ce\3\uffff";
	static final String DFA61_acceptS =
		"\33\uffff\1\1\1\2\1\3";
	static final String DFA61_specialS =
		"\36\uffff}>";
	static final String[] DFA61_transitionS = {
			"\1\1\10\uffff\1\2\5\uffff\2\4\4\uffff\1\4\1\uffff\1\5\3\uffff\1\6\1\7"+
			"\1\10\1\uffff\1\4\1\32\1\4\1\uffff\2\4\1\32\1\11\1\uffff\1\4\1\uffff"+
			"\1\30\1\12\4\uffff\1\32\1\13\1\uffff\1\14\2\uffff\3\4\1\15\1\uffff\1"+
			"\4\1\uffff\2\4\1\uffff\1\4\3\uffff\1\16\2\4\1\uffff\1\17\2\uffff\2\32"+
			"\1\4\1\uffff\3\4\1\uffff\3\4\6\uffff\1\4\1\uffff\1\4\4\uffff\1\4\2\uffff"+
			"\5\4\5\uffff\1\4\1\uffff\2\4\2\uffff\1\4\1\20\4\4\1\21\1\31\1\22\1\27"+
			"\1\23\2\uffff\1\4\1\uffff\1\32\2\4\4\uffff\2\4\1\uffff\1\24\1\4\1\25"+
			"\1\26\3\uffff\1\32\11\uffff\1\3",
			"\1\33\171\uffff\1\33\2\uffff\1\35\10\uffff\1\34",
			"\1\33\171\uffff\1\33\2\uffff\1\35\10\uffff\1\34",
			"\1\33\171\uffff\1\33\2\uffff\1\35\10\uffff\1\34",
			"\1\33\171\uffff\1\33\2\uffff\1\35\10\uffff\1\34",
			"\1\33\171\uffff\1\33\2\uffff\1\35\10\uffff\1\34",
			"\1\33\171\uffff\1\33\2\uffff\1\35\10\uffff\1\34",
			"\1\33\171\uffff\1\33\2\uffff\1\35\10\uffff\1\34",
			"\1\33\171\uffff\1\33\2\uffff\1\35\10\uffff\1\34",
			"\1\33\171\uffff\1\33\2\uffff\1\35\10\uffff\1\34",
			"\1\33\171\uffff\1\33\2\uffff\1\35\10\uffff\1\34",
			"\1\33\171\uffff\1\33\2\uffff\1\35\10\uffff\1\34",
			"\1\33\171\uffff\1\33\2\uffff\1\35\10\uffff\1\34",
			"\1\33\171\uffff\1\33\2\uffff\1\35\10\uffff\1\34",
			"\1\33\171\uffff\1\33\2\uffff\1\35\10\uffff\1\34",
			"\1\33\171\uffff\1\33\2\uffff\1\35\10\uffff\1\34",
			"\1\33\171\uffff\1\33\2\uffff\1\35\10\uffff\1\34",
			"\1\33\171\uffff\1\33\2\uffff\1\35\10\uffff\1\34",
			"\1\33\171\uffff\1\33\2\uffff\1\35\10\uffff\1\34",
			"\1\33\171\uffff\1\33\2\uffff\1\35\10\uffff\1\34",
			"\1\33\171\uffff\1\33\2\uffff\1\35\10\uffff\1\34",
			"\1\33\171\uffff\1\33\2\uffff\1\35\10\uffff\1\34",
			"\1\33\171\uffff\1\33\2\uffff\1\35\10\uffff\1\34",
			"\1\33\171\uffff\1\33\2\uffff\1\35\10\uffff\1\34",
			"\1\33\171\uffff\1\33\2\uffff\1\35\10\uffff\1\34",
			"\1\33\171\uffff\1\33\2\uffff\1\35\10\uffff\1\34",
			"\1\33\171\uffff\1\33\2\uffff\1\35\10\uffff\1\34",
			"",
			"",
			""
	};

	static final short[] DFA61_eot = DFA.unpackEncodedString(DFA61_eotS);
	static final short[] DFA61_eof = DFA.unpackEncodedString(DFA61_eofS);
	static final char[] DFA61_min = DFA.unpackEncodedStringToUnsignedChars(DFA61_minS);
	static final char[] DFA61_max = DFA.unpackEncodedStringToUnsignedChars(DFA61_maxS);
	static final short[] DFA61_accept = DFA.unpackEncodedString(DFA61_acceptS);
	static final short[] DFA61_special = DFA.unpackEncodedString(DFA61_specialS);
	static final short[][] DFA61_transition;

	static {
		int numStates = DFA61_transitionS.length;
		DFA61_transition = new short[numStates][];
		for (int i=0; i<numStates; i++) {
			DFA61_transition[i] = DFA.unpackEncodedString(DFA61_transitionS[i]);
		}
	}

	protected class DFA61 extends DFA {

		public DFA61(BaseRecognizer recognizer) {
			this.recognizer = recognizer;
			this.decisionNumber = 61;
			this.eot = DFA61_eot;
			this.eof = DFA61_eof;
			this.min = DFA61_min;
			this.max = DFA61_max;
			this.accept = DFA61_accept;
			this.special = DFA61_special;
			this.transition = DFA61_transition;
		}
		@Override
		public String getDescription() {
			return "596:1: deleteOp returns [Operation.RawDeletion op] : (c= cident |c= cident '[' t= term ']' |c= cident '.' field= fident );";
		}
	}

	static final String DFA174_eotS =
		"\35\uffff";
	static final String DFA174_eofS =
		"\1\uffff\32\34\2\uffff";
	static final String DFA174_minS =
		"\1\27\32\u00c5\2\uffff";
	static final String DFA174_maxS =
		"\1\u00ae\32\u00c8\2\uffff";
	static final String DFA174_acceptS =
		"\33\uffff\1\1\1\2";
	static final String DFA174_specialS =
		"\35\uffff}>";
	static final String[] DFA174_transitionS = {
			"\1\1\5\uffff\2\3\4\uffff\1\3\1\uffff\1\4\3\uffff\1\5\1\6\1\7\1\uffff"+
			"\1\3\1\31\1\3\1\uffff\2\3\1\31\1\10\1\uffff\1\3\1\uffff\1\27\1\11\4\uffff"+
			"\1\31\1\12\1\uffff\1\13\2\uffff\3\3\1\14\1\uffff\1\3\1\uffff\2\3\1\uffff"+
			"\1\3\3\uffff\1\15\2\3\1\uffff\1\16\2\uffff\2\31\1\3\1\uffff\3\3\1\uffff"+
			"\3\3\6\uffff\1\3\1\uffff\1\3\4\uffff\1\3\2\uffff\5\3\5\uffff\1\3\1\uffff"+
			"\2\3\2\uffff\1\3\1\17\4\3\1\20\1\30\1\21\1\26\1\22\2\uffff\1\3\1\uffff"+
			"\1\31\2\3\4\uffff\2\3\1\uffff\1\23\1\3\1\24\1\25\3\uffff\1\31\10\uffff"+
			"\1\32\1\2",
			"\1\33\2\uffff\1\34",
			"\1\33\2\uffff\1\34",
			"\1\33\2\uffff\1\34",
			"\1\33\2\uffff\1\34",
			"\1\33\2\uffff\1\34",
			"\1\33\2\uffff\1\34",
			"\1\33\2\uffff\1\34",
			"\1\33\2\uffff\1\34",
			"\1\33\2\uffff\1\34",
			"\1\33\2\uffff\1\34",
			"\1\33\2\uffff\1\34",
			"\1\33\2\uffff\1\34",
			"\1\33\2\uffff\1\34",
			"\1\33\2\uffff\1\34",
			"\1\33\2\uffff\1\34",
			"\1\33\2\uffff\1\34",
			"\1\33\2\uffff\1\34",
			"\1\33\2\uffff\1\34",
			"\1\33\2\uffff\1\34",
			"\1\33\2\uffff\1\34",
			"\1\33\2\uffff\1\34",
			"\1\33\2\uffff\1\34",
			"\1\33\2\uffff\1\34",
			"\1\33\2\uffff\1\34",
			"\1\33\2\uffff\1\34",
			"\1\33\2\uffff\1\34",
			"",
			""
	};

	static final short[] DFA174_eot = DFA.unpackEncodedString(DFA174_eotS);
	static final short[] DFA174_eof = DFA.unpackEncodedString(DFA174_eofS);
	static final char[] DFA174_min = DFA.unpackEncodedStringToUnsignedChars(DFA174_minS);
	static final char[] DFA174_max = DFA.unpackEncodedStringToUnsignedChars(DFA174_maxS);
	static final short[] DFA174_accept = DFA.unpackEncodedString(DFA174_acceptS);
	static final short[] DFA174_special = DFA.unpackEncodedString(DFA174_specialS);
	static final short[][] DFA174_transition;

	static {
		int numStates = DFA174_transitionS.length;
		DFA174_transition = new short[numStates][];
		for (int i=0; i<numStates; i++) {
			DFA174_transition[i] = DFA.unpackEncodedString(DFA174_transitionS[i]);
		}
	}

	protected class DFA174 extends DFA {

		public DFA174(BaseRecognizer recognizer) {
			this.recognizer = recognizer;
			this.decisionNumber = 174;
			this.eot = DFA174_eot;
			this.eof = DFA174_eof;
			this.min = DFA174_min;
			this.max = DFA174_max;
			this.accept = DFA174_accept;
			this.special = DFA174_special;
			this.transition = DFA174_transition;
		}
		@Override
		public String getDescription() {
			return "1351:7: ( ksName[name] '.' )?";
		}
	}

	static final String DFA175_eotS =
		"\35\uffff";
	static final String DFA175_eofS =
		"\1\uffff\32\34\2\uffff";
	static final String DFA175_minS =
		"\1\27\32\34\2\uffff";
	static final String DFA175_maxS =
		"\1\u00ae\32\u00c8\2\uffff";
	static final String DFA175_acceptS =
		"\33\uffff\1\1\1\2";
	static final String DFA175_specialS =
		"\35\uffff}>";
	static final String[] DFA175_transitionS = {
			"\1\1\5\uffff\2\3\4\uffff\1\3\1\uffff\1\4\3\uffff\1\5\1\6\1\7\1\uffff"+
			"\1\3\1\31\1\3\1\uffff\2\3\1\31\1\10\1\uffff\1\3\1\uffff\1\27\1\11\4\uffff"+
			"\1\31\1\12\1\uffff\1\13\2\uffff\3\3\1\14\1\uffff\1\3\1\uffff\2\3\1\uffff"+
			"\1\3\3\uffff\1\15\2\3\1\uffff\1\16\2\uffff\2\31\1\3\1\uffff\3\3\1\uffff"+
			"\3\3\6\uffff\1\3\1\uffff\1\3\4\uffff\1\3\2\uffff\5\3\5\uffff\1\3\1\uffff"+
			"\2\3\2\uffff\1\3\1\17\4\3\1\20\1\30\1\21\1\26\1\22\2\uffff\1\3\1\uffff"+
			"\1\31\2\3\4\uffff\2\3\1\uffff\1\23\1\3\1\24\1\25\3\uffff\1\31\10\uffff"+
			"\1\32\1\2",
			"\1\34\2\uffff\2\34\2\uffff\1\34\34\uffff\1\34\7\uffff\1\34\5\uffff\1"+
			"\34\12\uffff\1\34\6\uffff\1\34\12\uffff\1\34\3\uffff\1\34\3\uffff\1\34"+
			"\2\uffff\1\34\4\uffff\2\34\6\uffff\1\34\13\uffff\1\34\14\uffff\1\34\5"+
			"\uffff\2\34\32\uffff\1\34\6\uffff\1\33\2\uffff\1\34",
			"\1\34\2\uffff\2\34\2\uffff\1\34\34\uffff\1\34\7\uffff\1\34\5\uffff\1"+
			"\34\12\uffff\1\34\6\uffff\1\34\12\uffff\1\34\3\uffff\1\34\3\uffff\1\34"+
			"\2\uffff\1\34\4\uffff\2\34\6\uffff\1\34\13\uffff\1\34\14\uffff\1\34\5"+
			"\uffff\2\34\32\uffff\1\34\6\uffff\1\33\2\uffff\1\34",
			"\1\34\2\uffff\2\34\2\uffff\1\34\34\uffff\1\34\7\uffff\1\34\5\uffff\1"+
			"\34\12\uffff\1\34\6\uffff\1\34\12\uffff\1\34\3\uffff\1\34\3\uffff\1\34"+
			"\2\uffff\1\34\4\uffff\2\34\6\uffff\1\34\13\uffff\1\34\14\uffff\1\34\5"+
			"\uffff\2\34\32\uffff\1\34\6\uffff\1\33\2\uffff\1\34",
			"\1\34\2\uffff\2\34\2\uffff\1\34\34\uffff\1\34\7\uffff\1\34\5\uffff\1"+
			"\34\12\uffff\1\34\6\uffff\1\34\12\uffff\1\34\3\uffff\1\34\3\uffff\1\34"+
			"\2\uffff\1\34\4\uffff\2\34\6\uffff\1\34\13\uffff\1\34\14\uffff\1\34\5"+
			"\uffff\2\34\32\uffff\1\34\6\uffff\1\33\2\uffff\1\34",
			"\1\34\2\uffff\2\34\2\uffff\1\34\34\uffff\1\34\7\uffff\1\34\5\uffff\1"+
			"\34\12\uffff\1\34\6\uffff\1\34\12\uffff\1\34\3\uffff\1\34\3\uffff\1\34"+
			"\2\uffff\1\34\4\uffff\2\34\6\uffff\1\34\13\uffff\1\34\14\uffff\1\34\5"+
			"\uffff\2\34\32\uffff\1\34\6\uffff\1\33\2\uffff\1\34",
			"\1\34\2\uffff\2\34\2\uffff\1\34\34\uffff\1\34\7\uffff\1\34\5\uffff\1"+
			"\34\12\uffff\1\34\6\uffff\1\34\12\uffff\1\34\3\uffff\1\34\3\uffff\1\34"+
			"\2\uffff\1\34\4\uffff\2\34\6\uffff\1\34\13\uffff\1\34\14\uffff\1\34\5"+
			"\uffff\2\34\32\uffff\1\34\6\uffff\1\33\2\uffff\1\34",
			"\1\34\2\uffff\2\34\2\uffff\1\34\34\uffff\1\34\7\uffff\1\34\5\uffff\1"+
			"\34\12\uffff\1\34\6\uffff\1\34\12\uffff\1\34\3\uffff\1\34\3\uffff\1\34"+
			"\2\uffff\1\34\4\uffff\2\34\6\uffff\1\34\13\uffff\1\34\14\uffff\1\34\5"+
			"\uffff\2\34\32\uffff\1\34\6\uffff\1\33\2\uffff\1\34",
			"\1\34\2\uffff\2\34\2\uffff\1\34\34\uffff\1\34\7\uffff\1\34\5\uffff\1"+
			"\34\12\uffff\1\34\6\uffff\1\34\12\uffff\1\34\3\uffff\1\34\3\uffff\1\34"+
			"\2\uffff\1\34\4\uffff\2\34\6\uffff\1\34\13\uffff\1\34\14\uffff\1\34\5"+
			"\uffff\2\34\32\uffff\1\34\6\uffff\1\33\2\uffff\1\34",
			"\1\34\2\uffff\2\34\2\uffff\1\34\34\uffff\1\34\7\uffff\1\34\5\uffff\1"+
			"\34\12\uffff\1\34\6\uffff\1\34\12\uffff\1\34\3\uffff\1\34\3\uffff\1\34"+
			"\2\uffff\1\34\4\uffff\2\34\6\uffff\1\34\13\uffff\1\34\14\uffff\1\34\5"+
			"\uffff\2\34\32\uffff\1\34\6\uffff\1\33\2\uffff\1\34",
			"\1\34\2\uffff\2\34\2\uffff\1\34\34\uffff\1\34\7\uffff\1\34\5\uffff\1"+
			"\34\12\uffff\1\34\6\uffff\1\34\12\uffff\1\34\3\uffff\1\34\3\uffff\1\34"+
			"\2\uffff\1\34\4\uffff\2\34\6\uffff\1\34\13\uffff\1\34\14\uffff\1\34\5"+
			"\uffff\2\34\32\uffff\1\34\6\uffff\1\33\2\uffff\1\34",
			"\1\34\2\uffff\2\34\2\uffff\1\34\34\uffff\1\34\7\uffff\1\34\5\uffff\1"+
			"\34\12\uffff\1\34\6\uffff\1\34\12\uffff\1\34\3\uffff\1\34\3\uffff\1\34"+
			"\2\uffff\1\34\4\uffff\2\34\6\uffff\1\34\13\uffff\1\34\14\uffff\1\34\5"+
			"\uffff\2\34\32\uffff\1\34\6\uffff\1\33\2\uffff\1\34",
			"\1\34\2\uffff\2\34\2\uffff\1\34\34\uffff\1\34\7\uffff\1\34\5\uffff\1"+
			"\34\12\uffff\1\34\6\uffff\1\34\12\uffff\1\34\3\uffff\1\34\3\uffff\1\34"+
			"\2\uffff\1\34\4\uffff\2\34\6\uffff\1\34\13\uffff\1\34\14\uffff\1\34\5"+
			"\uffff\2\34\32\uffff\1\34\6\uffff\1\33\2\uffff\1\34",
			"\1\34\2\uffff\2\34\2\uffff\1\34\34\uffff\1\34\7\uffff\1\34\5\uffff\1"+
			"\34\12\uffff\1\34\6\uffff\1\34\12\uffff\1\34\3\uffff\1\34\3\uffff\1\34"+
			"\2\uffff\1\34\4\uffff\2\34\6\uffff\1\34\13\uffff\1\34\14\uffff\1\34\5"+
			"\uffff\2\34\32\uffff\1\34\6\uffff\1\33\2\uffff\1\34",
			"\1\34\2\uffff\2\34\2\uffff\1\34\34\uffff\1\34\7\uffff\1\34\5\uffff\1"+
			"\34\12\uffff\1\34\6\uffff\1\34\12\uffff\1\34\3\uffff\1\34\3\uffff\1\34"+
			"\2\uffff\1\34\4\uffff\2\34\6\uffff\1\34\13\uffff\1\34\14\uffff\1\34\5"+
			"\uffff\2\34\32\uffff\1\34\6\uffff\1\33\2\uffff\1\34",
			"\1\34\2\uffff\2\34\2\uffff\1\34\34\uffff\1\34\7\uffff\1\34\5\uffff\1"+
			"\34\12\uffff\1\34\6\uffff\1\34\12\uffff\1\34\3\uffff\1\34\3\uffff\1\34"+
			"\2\uffff\1\34\4\uffff\2\34\6\uffff\1\34\13\uffff\1\34\14\uffff\1\34\5"+
			"\uffff\2\34\32\uffff\1\34\6\uffff\1\33\2\uffff\1\34",
			"\1\34\2\uffff\2\34\2\uffff\1\34\34\uffff\1\34\7\uffff\1\34\5\uffff\1"+
			"\34\12\uffff\1\34\6\uffff\1\34\12\uffff\1\34\3\uffff\1\34\3\uffff\1\34"+
			"\2\uffff\1\34\4\uffff\2\34\6\uffff\1\34\13\uffff\1\34\14\uffff\1\34\5"+
			"\uffff\2\34\32\uffff\1\34\6\uffff\1\33\2\uffff\1\34",
			"\1\34\2\uffff\2\34\2\uffff\1\34\34\uffff\1\34\7\uffff\1\34\5\uffff\1"+
			"\34\12\uffff\1\34\6\uffff\1\34\12\uffff\1\34\3\uffff\1\34\3\uffff\1\34"+
			"\2\uffff\1\34\4\uffff\2\34\6\uffff\1\34\13\uffff\1\34\14\uffff\1\34\5"+
			"\uffff\2\34\32\uffff\1\34\6\uffff\1\33\2\uffff\1\34",
			"\1\34\2\uffff\2\34\2\uffff\1\34\34\uffff\1\34\7\uffff\1\34\5\uffff\1"+
			"\34\12\uffff\1\34\6\uffff\1\34\12\uffff\1\34\3\uffff\1\34\3\uffff\1\34"+
			"\2\uffff\1\34\4\uffff\2\34\6\uffff\1\34\13\uffff\1\34\14\uffff\1\34\5"+
			"\uffff\2\34\32\uffff\1\34\6\uffff\1\33\2\uffff\1\34",
			"\1\34\2\uffff\2\34\2\uffff\1\34\34\uffff\1\34\7\uffff\1\34\5\uffff\1"+
			"\34\12\uffff\1\34\6\uffff\1\34\12\uffff\1\34\3\uffff\1\34\3\uffff\1\34"+
			"\2\uffff\1\34\4\uffff\2\34\6\uffff\1\34\13\uffff\1\34\14\uffff\1\34\5"+
			"\uffff\2\34\32\uffff\1\34\6\uffff\1\33\2\uffff\1\34",
			"\1\34\2\uffff\2\34\2\uffff\1\34\34\uffff\1\34\7\uffff\1\34\5\uffff\1"+
			"\34\12\uffff\1\34\6\uffff\1\34\12\uffff\1\34\3\uffff\1\34\3\uffff\1\34"+
			"\2\uffff\1\34\4\uffff\2\34\6\uffff\1\34\13\uffff\1\34\14\uffff\1\34\5"+
			"\uffff\2\34\32\uffff\1\34\6\uffff\1\33\2\uffff\1\34",
			"\1\34\2\uffff\2\34\2\uffff\1\34\34\uffff\1\34\7\uffff\1\34\5\uffff\1"+
			"\34\12\uffff\1\34\6\uffff\1\34\12\uffff\1\34\3\uffff\1\34\3\uffff\1\34"+
			"\2\uffff\1\34\4\uffff\2\34\6\uffff\1\34\13\uffff\1\34\14\uffff\1\34\5"+
			"\uffff\2\34\32\uffff\1\34\6\uffff\1\33\2\uffff\1\34",
			"\1\34\2\uffff\2\34\2\uffff\1\34\34\uffff\1\34\7\uffff\1\34\5\uffff\1"+
			"\34\12\uffff\1\34\6\uffff\1\34\12\uffff\1\34\3\uffff\1\34\3\uffff\1\34"+
			"\2\uffff\1\34\4\uffff\2\34\6\uffff\1\34\13\uffff\1\34\14\uffff\1\34\5"+
			"\uffff\2\34\32\uffff\1\34\6\uffff\1\33\2\uffff\1\34",
			"\1\34\2\uffff\2\34\2\uffff\1\34\34\uffff\1\34\7\uffff\1\34\5\uffff\1"+
			"\34\12\uffff\1\34\6\uffff\1\34\12\uffff\1\34\3\uffff\1\34\3\uffff\1\34"+
			"\2\uffff\1\34\4\uffff\2\34\6\uffff\1\34\13\uffff\1\34\14\uffff\1\34\5"+
			"\uffff\2\34\32\uffff\1\34\6\uffff\1\33\2\uffff\1\34",
			"\1\34\2\uffff\2\34\2\uffff\1\34\34\uffff\1\34\7\uffff\1\34\5\uffff\1"+
			"\34\12\uffff\1\34\6\uffff\1\34\12\uffff\1\34\3\uffff\1\34\3\uffff\1\34"+
			"\2\uffff\1\34\4\uffff\2\34\6\uffff\1\34\13\uffff\1\34\14\uffff\1\34\5"+
			"\uffff\2\34\32\uffff\1\34\6\uffff\1\33\2\uffff\1\34",
			"\1\34\2\uffff\2\34\2\uffff\1\34\34\uffff\1\34\7\uffff\1\34\5\uffff\1"+
			"\34\12\uffff\1\34\6\uffff\1\34\12\uffff\1\34\3\uffff\1\34\3\uffff\1\34"+
			"\2\uffff\1\34\4\uffff\2\34\6\uffff\1\34\13\uffff\1\34\14\uffff\1\34\5"+
			"\uffff\2\34\32\uffff\1\34\6\uffff\1\33\2\uffff\1\34",
			"\1\34\2\uffff\2\34\2\uffff\1\34\34\uffff\1\34\7\uffff\1\34\5\uffff\1"+
			"\34\12\uffff\1\34\6\uffff\1\34\12\uffff\1\34\3\uffff\1\34\3\uffff\1\34"+
			"\2\uffff\1\34\4\uffff\2\34\6\uffff\1\34\13\uffff\1\34\14\uffff\1\34\5"+
			"\uffff\2\34\32\uffff\1\34\6\uffff\1\33\2\uffff\1\34",
			"",
			""
	};

	static final short[] DFA175_eot = DFA.unpackEncodedString(DFA175_eotS);
	static final short[] DFA175_eof = DFA.unpackEncodedString(DFA175_eofS);
	static final char[] DFA175_min = DFA.unpackEncodedStringToUnsignedChars(DFA175_minS);
	static final char[] DFA175_max = DFA.unpackEncodedStringToUnsignedChars(DFA175_maxS);
	static final short[] DFA175_accept = DFA.unpackEncodedString(DFA175_acceptS);
	static final short[] DFA175_special = DFA.unpackEncodedString(DFA175_specialS);
	static final short[][] DFA175_transition;

	static {
		int numStates = DFA175_transitionS.length;
		DFA175_transition = new short[numStates][];
		for (int i=0; i<numStates; i++) {
			DFA175_transition[i] = DFA.unpackEncodedString(DFA175_transitionS[i]);
		}
	}

	protected class DFA175 extends DFA {

		public DFA175(BaseRecognizer recognizer) {
			this.recognizer = recognizer;
			this.decisionNumber = 175;
			this.eot = DFA175_eot;
			this.eof = DFA175_eof;
			this.min = DFA175_min;
			this.max = DFA175_max;
			this.accept = DFA175_accept;
			this.special = DFA175_special;
			this.transition = DFA175_transition;
		}
		@Override
		public String getDescription() {
			return "1356:7: ( ksName[name] '.' )?";
		}
	}

	static final String DFA193_eotS =
		"\43\uffff";
	static final String DFA193_eofS =
		"\43\uffff";
	static final String DFA193_minS =
		"\1\6\2\uffff\1\6\4\uffff\31\u00be\1\u00c5\1\uffff";
	static final String DFA193_maxS =
		"\1\u00d2\2\uffff\1\u00d3\4\uffff\32\u00c7\1\uffff";
	static final String DFA193_acceptS =
		"\1\uffff\1\1\1\2\1\uffff\1\4\1\5\1\6\1\7\32\uffff\1\3";
	static final String DFA193_specialS =
		"\43\uffff}>";
	static final String[] DFA193_transitionS = {
			"\1\1\4\uffff\1\1\5\uffff\1\1\3\uffff\1\1\2\uffff\1\1\117\uffff\2\1\4"+
			"\uffff\1\5\12\uffff\2\1\62\uffff\1\7\4\uffff\1\1\2\uffff\1\1\10\uffff"+
			"\1\4\10\uffff\1\6\6\uffff\1\2\3\uffff\1\3",
			"",
			"",
			"\1\2\4\uffff\1\2\5\uffff\1\2\3\uffff\1\2\1\uffff\1\10\1\2\4\uffff\2"+
			"\12\4\uffff\1\12\1\uffff\1\13\3\uffff\1\14\1\15\1\16\1\uffff\1\12\1\41"+
			"\1\12\1\uffff\2\12\1\40\1\17\1\uffff\1\12\1\uffff\1\36\1\20\4\uffff\1"+
			"\41\1\21\1\uffff\1\22\2\uffff\3\12\1\23\1\uffff\1\12\1\uffff\2\12\1\uffff"+
			"\1\12\3\uffff\1\24\2\12\1\uffff\1\25\2\uffff\2\41\1\12\1\uffff\3\12\1"+
			"\uffff\3\12\4\uffff\2\2\1\12\1\uffff\1\12\1\uffff\1\2\2\uffff\1\12\2"+
			"\uffff\5\12\2\2\3\uffff\1\12\1\uffff\2\12\2\uffff\1\12\1\26\4\12\1\27"+
			"\1\37\1\30\1\35\1\31\1\uffff\1\2\1\12\1\uffff\1\41\2\12\4\uffff\2\12"+
			"\1\uffff\1\32\1\12\1\33\1\34\3\uffff\1\41\10\uffff\1\2\1\11\3\uffff\1"+
			"\2\2\uffff\1\2\10\uffff\1\2\4\uffff\1\2\3\uffff\1\2\6\uffff\1\2\3\uffff"+
			"\2\2",
			"",
			"",
			"",
			"",
			"\1\2\6\uffff\1\2\1\uffff\1\42",
			"\1\2\6\uffff\1\2\1\uffff\1\42",
			"\1\2\6\uffff\1\2\1\uffff\1\42",
			"\1\2\6\uffff\1\2\1\uffff\1\42",
			"\1\2\6\uffff\1\2\1\uffff\1\42",
			"\1\2\6\uffff\1\2\1\uffff\1\42",
			"\1\2\6\uffff\1\2\1\uffff\1\42",
			"\1\2\6\uffff\1\2\1\uffff\1\42",
			"\1\2\6\uffff\1\2\1\uffff\1\42",
			"\1\2\6\uffff\1\2\1\uffff\1\42",
			"\1\2\6\uffff\1\2\1\uffff\1\42",
			"\1\2\6\uffff\1\2\1\uffff\1\42",
			"\1\2\6\uffff\1\2\1\uffff\1\42",
			"\1\2\6\uffff\1\2\1\uffff\1\42",
			"\1\2\6\uffff\1\2\1\uffff\1\42",
			"\1\2\6\uffff\1\2\1\uffff\1\42",
			"\1\2\6\uffff\1\2\1\uffff\1\42",
			"\1\2\6\uffff\1\2\1\uffff\1\42",
			"\1\2\6\uffff\1\2\1\uffff\1\42",
			"\1\2\6\uffff\1\2\1\uffff\1\42",
			"\1\2\6\uffff\1\2\1\uffff\1\42",
			"\1\2\6\uffff\1\2\1\uffff\1\42",
			"\1\2\6\uffff\1\2\1\uffff\1\42",
			"\1\2\6\uffff\1\2\1\uffff\1\42",
			"\1\2\6\uffff\1\2\1\uffff\1\42",
			"\1\2\1\uffff\1\42",
			""
	};

	static final short[] DFA193_eot = DFA.unpackEncodedString(DFA193_eotS);
	static final short[] DFA193_eof = DFA.unpackEncodedString(DFA193_eofS);
	static final char[] DFA193_min = DFA.unpackEncodedStringToUnsignedChars(DFA193_minS);
	static final char[] DFA193_max = DFA.unpackEncodedStringToUnsignedChars(DFA193_maxS);
	static final short[] DFA193_accept = DFA.unpackEncodedString(DFA193_acceptS);
	static final short[] DFA193_special = DFA.unpackEncodedString(DFA193_specialS);
	static final short[][] DFA193_transition;

	static {
		int numStates = DFA193_transitionS.length;
		DFA193_transition = new short[numStates][];
		for (int i=0; i<numStates; i++) {
			DFA193_transition[i] = DFA.unpackEncodedString(DFA193_transitionS[i]);
		}
	}

	protected class DFA193 extends DFA {

		public DFA193(BaseRecognizer recognizer) {
			this.recognizer = recognizer;
			this.decisionNumber = 193;
			this.eot = DFA193_eot;
			this.eof = DFA193_eof;
			this.min = DFA193_min;
			this.max = DFA193_max;
			this.accept = DFA193_accept;
			this.special = DFA193_special;
			this.transition = DFA193_transition;
		}
		@Override
		public String getDescription() {
			return "1461:1: value returns [Term.Raw value] : (c= constant |l= collectionLiteral |u= usertypeLiteral |t= tupleLiteral | K_NULL | ':' id= noncol_ident | QMARK );";
		}
	}

	static final String DFA195_eotS =
		"\34\uffff";
	static final String DFA195_eofS =
		"\1\uffff\31\33\2\uffff";
	static final String DFA195_minS =
		"\1\27\31\u00be\2\uffff";
	static final String DFA195_maxS =
		"\1\u00ae\31\u00c8\2\uffff";
	static final String DFA195_acceptS =
		"\32\uffff\1\1\1\2";
	static final String DFA195_specialS =
		"\34\uffff}>";
	static final String[] DFA195_transitionS = {
			"\1\1\5\uffff\2\3\4\uffff\1\3\1\uffff\1\4\3\uffff\1\5\1\6\1\7\1\uffff"+
			"\1\3\1\32\1\3\1\uffff\2\3\1\31\1\10\1\uffff\1\3\1\uffff\1\27\1\11\4\uffff"+
			"\1\32\1\12\1\uffff\1\13\2\uffff\3\3\1\14\1\uffff\1\3\1\uffff\2\3\1\uffff"+
			"\1\3\3\uffff\1\15\2\3\1\uffff\1\16\2\uffff\2\32\1\3\1\uffff\3\3\1\uffff"+
			"\3\3\6\uffff\1\3\1\uffff\1\3\4\uffff\1\3\2\uffff\5\3\5\uffff\1\3\1\uffff"+
			"\2\3\2\uffff\1\3\1\17\4\3\1\20\1\30\1\21\1\26\1\22\1\uffff\1\33\1\3\1"+
			"\uffff\1\32\2\3\4\uffff\2\3\1\uffff\1\23\1\3\1\24\1\25\3\uffff\1\32\10"+
			"\uffff\1\32\1\2",
			"\1\33\6\uffff\1\32\2\uffff\1\33",
			"\1\33\6\uffff\1\32\2\uffff\1\33",
			"\1\33\6\uffff\1\32\2\uffff\1\33",
			"\1\33\6\uffff\1\32\2\uffff\1\33",
			"\1\33\6\uffff\1\32\2\uffff\1\33",
			"\1\33\6\uffff\1\32\2\uffff\1\33",
			"\1\33\6\uffff\1\32\2\uffff\1\33",
			"\1\33\6\uffff\1\32\2\uffff\1\33",
			"\1\33\6\uffff\1\32\2\uffff\1\33",
			"\1\33\6\uffff\1\32\2\uffff\1\33",
			"\1\33\6\uffff\1\32\2\uffff\1\33",
			"\1\33\6\uffff\1\32\2\uffff\1\33",
			"\1\33\6\uffff\1\32\2\uffff\1\33",
			"\1\33\6\uffff\1\32\2\uffff\1\33",
			"\1\33\6\uffff\1\32\2\uffff\1\33",
			"\1\33\6\uffff\1\32\2\uffff\1\33",
			"\1\33\6\uffff\1\32\2\uffff\1\33",
			"\1\33\6\uffff\1\32\2\uffff\1\33",
			"\1\33\6\uffff\1\32\2\uffff\1\33",
			"\1\33\6\uffff\1\32\2\uffff\1\33",
			"\1\33\6\uffff\1\32\2\uffff\1\33",
			"\1\33\6\uffff\1\32\2\uffff\1\33",
			"\1\33\6\uffff\1\32\2\uffff\1\33",
			"\1\33\6\uffff\1\32\2\uffff\1\33",
			"\1\33\6\uffff\1\32\2\uffff\1\33",
			"",
			""
	};

	static final short[] DFA195_eot = DFA.unpackEncodedString(DFA195_eotS);
	static final short[] DFA195_eof = DFA.unpackEncodedString(DFA195_eofS);
	static final char[] DFA195_min = DFA.unpackEncodedStringToUnsignedChars(DFA195_minS);
	static final char[] DFA195_max = DFA.unpackEncodedStringToUnsignedChars(DFA195_maxS);
	static final short[] DFA195_accept = DFA.unpackEncodedString(DFA195_acceptS);
	static final short[] DFA195_special = DFA.unpackEncodedString(DFA195_specialS);
	static final short[][] DFA195_transition;

	static {
		int numStates = DFA195_transitionS.length;
		DFA195_transition = new short[numStates][];
		for (int i=0; i<numStates; i++) {
			DFA195_transition[i] = DFA.unpackEncodedString(DFA195_transitionS[i]);
		}
	}

	protected class DFA195 extends DFA {

		public DFA195(BaseRecognizer recognizer) {
			this.recognizer = recognizer;
			this.decisionNumber = 195;
			this.eot = DFA195_eot;
			this.eof = DFA195_eof;
			this.min = DFA195_min;
			this.max = DFA195_max;
			this.accept = DFA195_accept;
			this.special = DFA195_special;
			this.transition = DFA195_transition;
		}
		@Override
		public String getDescription() {
			return "1480:7: (ks= keyspaceName '.' )?";
		}
	}

	static final String DFA197_eotS =
		"\72\uffff";
	static final String DFA197_eofS =
		"\72\uffff";
	static final String DFA197_minS =
		"\1\27\31\u00be\1\u00c5\1\u00be\1\u00c5\1\27\1\6\31\u00be\2\uffff";
	static final String DFA197_maxS =
		"\1\u00ae\32\u00c5\1\u00be\1\u00c5\1\u00ae\1\u00d2\31\u00be\2\uffff";
	static final String DFA197_acceptS =
		"\70\uffff\1\1\1\2";
	static final String DFA197_specialS =
		"\72\uffff}>";
	static final String[] DFA197_transitionS = {
			"\1\1\5\uffff\2\3\4\uffff\1\3\1\uffff\1\4\3\uffff\1\5\1\6\1\7\1\uffff"+
			"\1\3\1\34\1\3\1\uffff\2\3\1\31\1\10\1\uffff\1\3\1\uffff\1\27\1\11\4\uffff"+
			"\1\34\1\12\1\uffff\1\13\2\uffff\3\3\1\14\1\uffff\1\3\1\uffff\2\3\1\uffff"+
			"\1\3\3\uffff\1\15\2\3\1\uffff\1\16\2\uffff\2\34\1\3\1\uffff\3\3\1\uffff"+
			"\3\3\6\uffff\1\3\1\uffff\1\3\4\uffff\1\3\2\uffff\5\3\5\uffff\1\3\1\uffff"+
			"\2\3\2\uffff\1\3\1\17\4\3\1\20\1\30\1\21\1\26\1\22\1\uffff\1\33\1\3\1"+
			"\uffff\1\34\2\3\4\uffff\2\3\1\uffff\1\23\1\3\1\24\1\25\3\uffff\1\34\10"+
			"\uffff\1\32\1\2",
			"\1\36\6\uffff\1\35",
			"\1\36\6\uffff\1\35",
			"\1\36\6\uffff\1\35",
			"\1\36\6\uffff\1\35",
			"\1\36\6\uffff\1\35",
			"\1\36\6\uffff\1\35",
			"\1\36\6\uffff\1\35",
			"\1\36\6\uffff\1\35",
			"\1\36\6\uffff\1\35",
			"\1\36\6\uffff\1\35",
			"\1\36\6\uffff\1\35",
			"\1\36\6\uffff\1\35",
			"\1\36\6\uffff\1\35",
			"\1\36\6\uffff\1\35",
			"\1\36\6\uffff\1\35",
			"\1\36\6\uffff\1\35",
			"\1\36\6\uffff\1\35",
			"\1\36\6\uffff\1\35",
			"\1\36\6\uffff\1\35",
			"\1\36\6\uffff\1\35",
			"\1\36\6\uffff\1\35",
			"\1\36\6\uffff\1\35",
			"\1\36\6\uffff\1\35",
			"\1\36\6\uffff\1\35",
			"\1\36\6\uffff\1\35",
			"\1\35",
			"\1\36",
			"\1\35",
			"\1\37\5\uffff\2\41\4\uffff\1\41\1\uffff\1\42\3\uffff\1\43\1\44\1\45"+
			"\1\uffff\1\41\1\uffff\1\41\1\uffff\2\41\1\67\1\46\1\uffff\1\41\1\uffff"+
			"\1\65\1\47\5\uffff\1\50\1\uffff\1\51\2\uffff\3\41\1\52\1\uffff\1\41\1"+
			"\uffff\2\41\1\uffff\1\41\3\uffff\1\53\2\41\1\uffff\1\54\4\uffff\1\41"+
			"\1\uffff\3\41\1\uffff\3\41\6\uffff\1\41\1\uffff\1\41\4\uffff\1\41\2\uffff"+
			"\5\41\5\uffff\1\41\1\uffff\2\41\2\uffff\1\41\1\55\4\41\1\56\1\66\1\57"+
			"\1\64\1\60\1\uffff\1\33\1\41\2\uffff\2\41\4\uffff\2\41\1\uffff\1\61\1"+
			"\41\1\62\1\63\15\uffff\1\40",
			"\1\71\4\uffff\1\71\5\uffff\1\71\3\uffff\1\71\1\uffff\2\71\4\uffff\2"+
			"\71\4\uffff\1\71\1\uffff\1\71\3\uffff\3\71\1\uffff\3\71\1\uffff\4\71"+
			"\1\uffff\1\71\1\uffff\2\71\4\uffff\2\71\1\uffff\1\71\2\uffff\4\71\1\uffff"+
			"\1\71\1\uffff\2\71\1\uffff\1\71\3\uffff\3\71\1\uffff\1\71\2\uffff\3\71"+
			"\1\uffff\3\71\1\uffff\3\71\4\uffff\3\71\1\uffff\1\71\1\uffff\1\71\2\uffff"+
			"\1\71\2\uffff\7\71\3\uffff\1\71\1\uffff\2\71\2\uffff\13\71\1\uffff\2"+
			"\71\1\uffff\3\71\4\uffff\2\71\1\uffff\4\71\3\uffff\1\71\10\uffff\2\71"+
			"\3\uffff\1\71\2\uffff\1\71\10\uffff\1\71\1\70\3\uffff\1\71\3\uffff\1"+
			"\71\6\uffff\1\71\3\uffff\1\71",
			"\1\36",
			"\1\36",
			"\1\36",
			"\1\36",
			"\1\36",
			"\1\36",
			"\1\36",
			"\1\36",
			"\1\36",
			"\1\36",
			"\1\36",
			"\1\36",
			"\1\36",
			"\1\36",
			"\1\36",
			"\1\36",
			"\1\36",
			"\1\36",
			"\1\36",
			"\1\36",
			"\1\36",
			"\1\36",
			"\1\36",
			"\1\36",
			"\1\36",
			"",
			""
	};

	static final short[] DFA197_eot = DFA.unpackEncodedString(DFA197_eotS);
	static final short[] DFA197_eof = DFA.unpackEncodedString(DFA197_eofS);
	static final char[] DFA197_min = DFA.unpackEncodedStringToUnsignedChars(DFA197_minS);
	static final char[] DFA197_max = DFA.unpackEncodedStringToUnsignedChars(DFA197_maxS);
	static final short[] DFA197_accept = DFA.unpackEncodedString(DFA197_acceptS);
	static final short[] DFA197_special = DFA.unpackEncodedString(DFA197_specialS);
	static final short[][] DFA197_transition;

	static {
		int numStates = DFA197_transitionS.length;
		DFA197_transition = new short[numStates][];
		for (int i=0; i<numStates; i++) {
			DFA197_transition[i] = DFA.unpackEncodedString(DFA197_transitionS[i]);
		}
	}

	protected class DFA197 extends DFA {

		public DFA197(BaseRecognizer recognizer) {
			this.recognizer = recognizer;
			this.decisionNumber = 197;
			this.eot = DFA197_eot;
			this.eof = DFA197_eof;
			this.min = DFA197_min;
			this.max = DFA197_max;
			this.accept = DFA197_accept;
			this.special = DFA197_special;
			this.transition = DFA197_transition;
		}
		@Override
		public String getDescription() {
			return "1491:1: function returns [Term.Raw t] : (f= functionName '(' ')' |f= functionName '(' args= functionArgs ')' );";
		}
	}

	static final String DFA199_eotS =
		"\37\uffff";
	static final String DFA199_eofS =
		"\1\1\36\uffff";
	static final String DFA199_minS =
		"\1\37\1\uffff\1\6\1\uffff\31\u00a2\1\uffff\1\u00a2";
	static final String DFA199_maxS =
		"\1\u00d3\1\uffff\1\u00d2\1\uffff\31\u00c5\1\uffff\1\u00c5";
	static final String DFA199_acceptS =
		"\1\uffff\1\3\1\uffff\1\2\31\uffff\1\1\1\uffff";
	static final String DFA199_specialS =
		"\37\uffff}>";
	static final String[] DFA199_transitionS = {
			"\1\1\1\uffff\2\1\30\uffff\1\1\22\uffff\2\1\5\uffff\1\1\12\uffff\1\1\22"+
			"\uffff\1\1\2\uffff\1\1\4\uffff\1\1\34\uffff\1\1\11\uffff\1\1\15\uffff"+
			"\1\1\16\uffff\1\1\1\2\1\uffff\1\1\1\3\3\uffff\2\1\7\uffff\1\1\2\uffff"+
			"\1\1",
			"",
			"\1\35\4\uffff\1\35\2\uffff\1\1\2\uffff\1\35\3\uffff\1\35\1\uffff\1\4"+
			"\1\35\4\uffff\2\6\4\uffff\1\6\1\uffff\1\7\3\uffff\1\10\1\11\1\12\1\uffff"+
			"\1\6\1\36\1\6\1\uffff\2\6\1\34\1\13\1\uffff\1\6\1\uffff\1\32\1\14\4\uffff"+
			"\1\36\1\15\1\uffff\1\16\2\uffff\3\6\1\17\1\uffff\1\6\1\uffff\2\6\1\uffff"+
			"\1\6\3\uffff\1\20\2\6\1\uffff\1\21\2\uffff\2\36\1\6\1\uffff\3\6\1\uffff"+
			"\3\6\4\uffff\2\35\1\6\1\uffff\1\6\1\uffff\1\35\2\uffff\1\6\2\uffff\5"+
			"\6\2\35\3\uffff\1\6\1\uffff\2\6\2\uffff\1\6\1\22\4\6\1\23\1\33\1\24\1"+
			"\31\1\25\1\uffff\1\35\1\6\1\uffff\1\36\2\6\4\uffff\2\6\1\uffff\1\26\1"+
			"\6\1\27\1\30\3\uffff\1\36\10\uffff\1\35\1\5\3\uffff\1\35\2\uffff\1\35"+
			"\10\uffff\1\35\4\uffff\1\35\3\uffff\1\35\6\uffff\1\35\3\uffff\1\35",
			"",
			"\1\1\33\uffff\1\35\3\uffff\1\1\2\uffff\1\35",
			"\1\1\33\uffff\1\35\3\uffff\1\1\2\uffff\1\35",
			"\1\1\33\uffff\1\35\3\uffff\1\1\2\uffff\1\35",
			"\1\1\33\uffff\1\35\3\uffff\1\1\2\uffff\1\35",
			"\1\1\33\uffff\1\35\3\uffff\1\1\2\uffff\1\35",
			"\1\1\33\uffff\1\35\3\uffff\1\1\2\uffff\1\35",
			"\1\1\33\uffff\1\35\3\uffff\1\1\2\uffff\1\35",
			"\1\1\33\uffff\1\35\3\uffff\1\1\2\uffff\1\35",
			"\1\1\33\uffff\1\35\3\uffff\1\1\2\uffff\1\35",
			"\1\1\33\uffff\1\35\3\uffff\1\1\2\uffff\1\35",
			"\1\1\33\uffff\1\35\3\uffff\1\1\2\uffff\1\35",
			"\1\1\33\uffff\1\35\3\uffff\1\1\2\uffff\1\35",
			"\1\1\33\uffff\1\35\3\uffff\1\1\2\uffff\1\35",
			"\1\1\33\uffff\1\35\3\uffff\1\1\2\uffff\1\35",
			"\1\1\33\uffff\1\35\3\uffff\1\1\2\uffff\1\35",
			"\1\1\33\uffff\1\35\3\uffff\1\1\2\uffff\1\35",
			"\1\1\33\uffff\1\35\3\uffff\1\1\2\uffff\1\35",
			"\1\1\33\uffff\1\35\3\uffff\1\1\2\uffff\1\35",
			"\1\1\33\uffff\1\35\3\uffff\1\1\2\uffff\1\35",
			"\1\1\33\uffff\1\35\3\uffff\1\1\2\uffff\1\35",
			"\1\1\33\uffff\1\35\3\uffff\1\1\2\uffff\1\35",
			"\1\1\33\uffff\1\35\3\uffff\1\1\2\uffff\1\35",
			"\1\1\33\uffff\1\35\3\uffff\1\1\2\uffff\1\35",
			"\1\1\33\uffff\1\35\3\uffff\1\1\2\uffff\1\35",
			"\1\1\33\uffff\1\35\3\uffff\1\1\2\uffff\1\35",
			"",
			"\1\1\37\uffff\1\1\2\uffff\1\35"
	};

	static final short[] DFA199_eot = DFA.unpackEncodedString(DFA199_eotS);
	static final short[] DFA199_eof = DFA.unpackEncodedString(DFA199_eofS);
	static final char[] DFA199_min = DFA.unpackEncodedStringToUnsignedChars(DFA199_minS);
	static final char[] DFA199_max = DFA.unpackEncodedStringToUnsignedChars(DFA199_maxS);
	static final short[] DFA199_accept = DFA.unpackEncodedString(DFA199_acceptS);
	static final short[] DFA199_special = DFA.unpackEncodedString(DFA199_specialS);
	static final short[][] DFA199_transition;

	static {
		int numStates = DFA199_transitionS.length;
		DFA199_transition = new short[numStates][];
		for (int i=0; i<numStates; i++) {
			DFA199_transition[i] = DFA.unpackEncodedString(DFA199_transitionS[i]);
		}
	}

	protected class DFA199 extends DFA {

		public DFA199(BaseRecognizer recognizer) {
			this.recognizer = recognizer;
			this.decisionNumber = 199;
			this.eot = DFA199_eot;
			this.eof = DFA199_eof;
			this.min = DFA199_min;
			this.max = DFA199_max;
			this.accept = DFA199_accept;
			this.special = DFA199_special;
			this.transition = DFA199_transition;
		}
		@Override
		public String getDescription() {
			return "()* loopback of 1507:9: ( '+' r= termMultiplication | '-' r= termMultiplication )*";
		}
	}

	static final String DFA202_eotS =
		"\110\uffff";
	static final String DFA202_eofS =
		"\3\uffff\1\1\42\uffff\1\1\7\uffff\32\42";
	static final String DFA202_minS =
		"\1\6\1\uffff\1\6\1\37\1\uffff\1\u00bd\31\u00be\1\u00bf\2\u00be\1\uffff"+
		"\1\u00be\1\u00c5\1\u00be\1\6\1\27\1\6\1\54\1\164\3\u00be\32\37";
	static final String DFA202_maxS =
		"\1\u00d2\1\uffff\1\u00d2\1\u00d3\1\uffff\1\u00cf\2\u00c5\1\u00c9\27\u00c5"+
		"\2\u00c9\1\uffff\1\u00c9\2\u00c5\1\u00d3\1\u00ae\1\u00d2\2\u00c5\3\u00bf"+
		"\32\u00d3";
	static final String DFA202_acceptS =
		"\1\uffff\1\1\2\uffff\1\2\35\uffff\1\3\45\uffff";
	static final String DFA202_specialS =
		"\110\uffff}>";
	static final String[] DFA202_transitionS = {
			"\1\1\4\uffff\1\1\5\uffff\1\1\3\uffff\1\1\1\uffff\1\4\1\1\4\uffff\2\4"+
			"\4\uffff\1\4\1\uffff\1\4\3\uffff\3\4\1\uffff\3\4\1\uffff\4\4\1\uffff"+
			"\1\4\1\uffff\2\4\4\uffff\2\4\1\uffff\1\4\2\uffff\4\4\1\uffff\1\4\1\uffff"+
			"\2\4\1\uffff\1\4\3\uffff\3\4\1\uffff\1\4\2\uffff\3\4\1\uffff\3\4\1\uffff"+
			"\3\4\4\uffff\2\1\1\4\1\uffff\1\4\1\uffff\1\1\2\uffff\1\4\2\uffff\5\4"+
			"\2\1\3\uffff\1\4\1\uffff\2\4\2\uffff\13\4\1\uffff\2\4\1\uffff\3\4\4\uffff"+
			"\2\4\1\uffff\4\4\3\uffff\1\4\10\uffff\1\3\1\4\3\uffff\1\1\2\uffff\1\1"+
			"\10\uffff\1\2\10\uffff\1\1\6\uffff\1\1\3\uffff\1\1",
			"",
			"\1\1\4\uffff\1\1\5\uffff\1\1\3\uffff\1\1\1\uffff\1\6\1\1\4\uffff\2\45"+
			"\4\uffff\1\45\1\uffff\1\11\3\uffff\1\12\1\13\1\14\1\uffff\1\45\1\44\1"+
			"\45\1\uffff\2\45\1\36\1\15\1\uffff\1\45\1\uffff\1\34\1\16\4\uffff\1\44"+
			"\1\17\1\uffff\1\20\2\uffff\3\45\1\21\1\uffff\1\43\1\uffff\2\45\1\uffff"+
			"\1\45\3\uffff\1\22\2\45\1\uffff\1\23\2\uffff\1\44\1\37\1\45\1\uffff\3"+
			"\45\1\uffff\1\40\1\45\1\10\4\uffff\2\1\1\45\1\uffff\1\45\1\uffff\1\1"+
			"\2\uffff\1\45\2\uffff\5\45\2\1\3\uffff\1\45\1\uffff\2\45\1\uffff\1\42"+
			"\1\45\1\24\4\45\1\25\1\35\1\26\1\33\1\27\1\uffff\1\1\1\45\1\uffff\1\44"+
			"\1\41\1\45\4\uffff\2\45\1\uffff\1\30\1\45\1\31\1\32\3\uffff\1\44\10\uffff"+
			"\1\1\1\7\3\uffff\1\5\2\uffff\1\1\10\uffff\1\1\4\uffff\1\1\3\uffff\1\1"+
			"\6\uffff\1\1\3\uffff\1\1",
			"\1\1\1\uffff\2\1\30\uffff\1\1\22\uffff\2\1\5\uffff\1\1\12\uffff\1\1"+
			"\22\uffff\1\1\2\uffff\1\1\4\uffff\1\1\34\uffff\1\1\11\uffff\1\1\15\uffff"+
			"\1\1\14\uffff\1\1\1\uffff\2\1\1\uffff\2\1\1\uffff\1\4\3\1\6\uffff\2\1"+
			"\2\uffff\1\1",
			"",
			"\1\1\1\uffff\1\46\1\1\1\uffff\2\1\2\uffff\1\1\10\uffff\1\1",
			"\1\1\1\42\5\uffff\1\47",
			"\1\1\1\42\5\uffff\1\47",
			"\1\1\1\42\5\uffff\1\47\3\uffff\1\42",
			"\1\1\1\42\5\uffff\1\47",
			"\1\1\1\42\5\uffff\1\47",
			"\1\1\1\42\5\uffff\1\47",
			"\1\1\1\42\5\uffff\1\47",
			"\1\1\1\42\5\uffff\1\47",
			"\1\1\1\42\5\uffff\1\47",
			"\1\1\1\42\5\uffff\1\47",
			"\1\1\1\42\5\uffff\1\47",
			"\1\1\1\42\5\uffff\1\47",
			"\1\1\1\42\5\uffff\1\47",
			"\1\1\1\42\5\uffff\1\47",
			"\1\1\1\42\5\uffff\1\47",
			"\1\1\1\42\5\uffff\1\47",
			"\1\1\1\42\5\uffff\1\47",
			"\1\1\1\42\5\uffff\1\47",
			"\1\1\1\42\5\uffff\1\47",
			"\1\1\1\42\5\uffff\1\47",
			"\1\1\1\42\5\uffff\1\47",
			"\1\1\1\42\5\uffff\1\47",
			"\1\1\1\42\5\uffff\1\47",
			"\1\1\1\42\5\uffff\1\47",
			"\1\1\6\uffff\1\47",
			"\1\42\5\uffff\1\47",
			"\1\1\1\42\5\uffff\1\47\3\uffff\1\42",
			"\1\1\1\42\5\uffff\1\47\3\uffff\1\42",
			"",
			"\1\1\1\42\5\uffff\1\47\3\uffff\1\42",
			"\1\47",
			"\1\1\1\42\5\uffff\1\47",
			"\1\42\4\uffff\1\42\5\uffff\1\42\3\uffff\1\42\1\uffff\2\42\4\uffff\2"+
			"\42\1\1\1\uffff\2\1\1\42\1\uffff\1\42\3\uffff\3\42\1\uffff\3\42\1\uffff"+
			"\4\42\1\uffff\1\42\1\uffff\2\42\1\uffff\1\1\2\uffff\2\42\1\uffff\1\42"+
			"\2\uffff\4\42\1\uffff\1\42\1\uffff\2\42\1\uffff\1\51\1\1\2\uffff\3\42"+
			"\1\1\1\42\2\uffff\3\42\1\uffff\3\42\1\1\3\42\4\uffff\3\42\1\uffff\1\42"+
			"\1\uffff\1\42\2\uffff\1\42\1\uffff\1\1\2\42\1\52\4\42\1\1\2\uffff\1\42"+
			"\1\uffff\2\42\2\uffff\13\42\1\uffff\2\42\1\uffff\3\42\2\uffff\1\1\1\uffff"+
			"\2\42\1\uffff\4\42\1\uffff\1\1\1\uffff\1\42\10\uffff\2\42\1\uffff\1\1"+
			"\1\uffff\1\42\2\uffff\1\42\7\uffff\1\1\1\42\2\1\1\uffff\2\1\2\uffff\1"+
			"\1\1\50\1\1\5\uffff\1\42\2\1\1\uffff\1\42\1\1",
			"\1\53\5\uffff\2\55\4\uffff\1\55\1\uffff\1\1\3\uffff\3\1\1\uffff\1\55"+
			"\1\uffff\1\55\1\uffff\2\55\2\1\1\uffff\1\55\1\uffff\2\1\5\uffff\1\1\1"+
			"\uffff\1\1\2\uffff\3\55\1\1\1\uffff\1\55\1\uffff\2\55\1\uffff\1\55\3"+
			"\uffff\1\1\2\55\1\uffff\1\1\3\uffff\1\42\1\55\1\uffff\3\55\1\uffff\3"+
			"\55\6\uffff\1\55\1\uffff\1\55\4\uffff\1\55\2\uffff\5\55\5\uffff\1\55"+
			"\1\uffff\2\55\2\uffff\1\55\1\1\4\55\5\1\1\uffff\1\1\1\55\2\uffff\2\55"+
			"\4\uffff\2\55\1\uffff\1\1\1\55\2\1\15\uffff\1\54",
			"\1\1\4\uffff\1\1\5\uffff\1\1\3\uffff\1\1\1\uffff\1\56\1\1\4\uffff\2"+
			"\60\4\uffff\1\60\1\uffff\1\61\3\uffff\1\62\1\63\1\64\1\uffff\1\60\1\107"+
			"\1\60\1\uffff\2\60\1\106\1\65\1\uffff\1\60\1\uffff\1\104\1\66\4\uffff"+
			"\1\107\1\67\1\uffff\1\70\2\uffff\3\60\1\71\1\uffff\1\60\1\uffff\2\60"+
			"\1\uffff\1\60\3\uffff\1\72\2\60\1\uffff\1\73\2\uffff\2\107\1\60\1\uffff"+
			"\3\60\1\uffff\3\60\4\uffff\2\1\1\60\1\uffff\1\60\1\uffff\1\1\2\uffff"+
			"\1\60\2\uffff\5\60\2\1\3\uffff\1\60\1\uffff\2\60\2\uffff\1\60\1\74\4"+
			"\60\1\75\1\105\1\76\1\103\1\77\1\uffff\1\1\1\60\1\uffff\1\107\2\60\4"+
			"\uffff\2\60\1\uffff\1\100\1\60\1\101\1\102\3\uffff\1\107\10\uffff\1\1"+
			"\1\57\3\uffff\1\1\2\uffff\1\1\10\uffff\1\1\4\uffff\1\1\3\uffff\1\1\6"+
			"\uffff\1\1\3\uffff\1\1",
			"\1\1\u0091\uffff\1\42\6\uffff\1\42",
			"\1\1\111\uffff\1\42\6\uffff\1\42",
			"\1\1\1\42",
			"\1\1\1\42",
			"\1\1\1\42",
			"\1\42\1\uffff\2\42\30\uffff\1\42\22\uffff\2\42\5\uffff\1\42\12\uffff"+
			"\1\42\22\uffff\1\42\2\uffff\1\42\4\uffff\1\42\34\uffff\1\42\11\uffff"+
			"\1\42\15\uffff\1\42\14\uffff\1\42\1\1\2\42\1\uffff\2\42\1\uffff\1\1\3"+
			"\42\6\uffff\2\42\2\uffff\1\42",
			"\1\42\1\uffff\2\42\30\uffff\1\42\22\uffff\2\42\5\uffff\1\42\12\uffff"+
			"\1\42\22\uffff\1\42\2\uffff\1\42\4\uffff\1\42\34\uffff\1\42\11\uffff"+
			"\1\42\15\uffff\1\42\14\uffff\1\42\1\1\2\42\1\uffff\2\42\1\uffff\1\1\3"+
			"\42\6\uffff\2\42\2\uffff\1\42",
			"\1\42\1\uffff\2\42\30\uffff\1\42\22\uffff\2\42\5\uffff\1\42\12\uffff"+
			"\1\42\22\uffff\1\42\2\uffff\1\42\4\uffff\1\42\34\uffff\1\42\11\uffff"+
			"\1\42\15\uffff\1\42\14\uffff\1\42\1\1\2\42\1\uffff\2\42\1\uffff\1\1\3"+
			"\42\6\uffff\2\42\2\uffff\1\42",
			"\1\42\1\uffff\2\42\30\uffff\1\42\22\uffff\2\42\5\uffff\1\42\12\uffff"+
			"\1\42\22\uffff\1\42\2\uffff\1\42\4\uffff\1\42\34\uffff\1\42\11\uffff"+
			"\1\42\15\uffff\1\42\14\uffff\1\42\1\1\2\42\1\uffff\2\42\1\uffff\1\1\3"+
			"\42\6\uffff\2\42\2\uffff\1\42",
			"\1\42\1\uffff\2\42\30\uffff\1\42\22\uffff\2\42\5\uffff\1\42\12\uffff"+
			"\1\42\22\uffff\1\42\2\uffff\1\42\4\uffff\1\42\34\uffff\1\42\11\uffff"+
			"\1\42\15\uffff\1\42\14\uffff\1\42\1\1\2\42\1\uffff\2\42\1\uffff\1\1\3"+
			"\42\6\uffff\2\42\2\uffff\1\42",
			"\1\42\1\uffff\2\42\30\uffff\1\42\22\uffff\2\42\5\uffff\1\42\12\uffff"+
			"\1\42\22\uffff\1\42\2\uffff\1\42\4\uffff\1\42\34\uffff\1\42\11\uffff"+
			"\1\42\15\uffff\1\42\14\uffff\1\42\1\1\2\42\1\uffff\2\42\1\uffff\1\1\3"+
			"\42\6\uffff\2\42\2\uffff\1\42",
			"\1\42\1\uffff\2\42\30\uffff\1\42\22\uffff\2\42\5\uffff\1\42\12\uffff"+
			"\1\42\22\uffff\1\42\2\uffff\1\42\4\uffff\1\42\34\uffff\1\42\11\uffff"+
			"\1\42\15\uffff\1\42\14\uffff\1\42\1\1\2\42\1\uffff\2\42\1\uffff\1\1\3"+
			"\42\6\uffff\2\42\2\uffff\1\42",
			"\1\42\1\uffff\2\42\30\uffff\1\42\22\uffff\2\42\5\uffff\1\42\12\uffff"+
			"\1\42\22\uffff\1\42\2\uffff\1\42\4\uffff\1\42\34\uffff\1\42\11\uffff"+
			"\1\42\15\uffff\1\42\14\uffff\1\42\1\1\2\42\1\uffff\2\42\1\uffff\1\1\3"+
			"\42\6\uffff\2\42\2\uffff\1\42",
			"\1\42\1\uffff\2\42\30\uffff\1\42\22\uffff\2\42\5\uffff\1\42\12\uffff"+
			"\1\42\22\uffff\1\42\2\uffff\1\42\4\uffff\1\42\34\uffff\1\42\11\uffff"+
			"\1\42\15\uffff\1\42\14\uffff\1\42\1\1\2\42\1\uffff\2\42\1\uffff\1\1\3"+
			"\42\6\uffff\2\42\2\uffff\1\42",
			"\1\42\1\uffff\2\42\30\uffff\1\42\22\uffff\2\42\5\uffff\1\42\12\uffff"+
			"\1\42\22\uffff\1\42\2\uffff\1\42\4\uffff\1\42\34\uffff\1\42\11\uffff"+
			"\1\42\15\uffff\1\42\14\uffff\1\42\1\1\2\42\1\uffff\2\42\1\uffff\1\1\3"+
			"\42\6\uffff\2\42\2\uffff\1\42",
			"\1\42\1\uffff\2\42\30\uffff\1\42\22\uffff\2\42\5\uffff\1\42\12\uffff"+
			"\1\42\22\uffff\1\42\2\uffff\1\42\4\uffff\1\42\34\uffff\1\42\11\uffff"+
			"\1\42\15\uffff\1\42\14\uffff\1\42\1\1\2\42\1\uffff\2\42\1\uffff\1\1\3"+
			"\42\6\uffff\2\42\2\uffff\1\42",
			"\1\42\1\uffff\2\42\30\uffff\1\42\22\uffff\2\42\5\uffff\1\42\12\uffff"+
			"\1\42\22\uffff\1\42\2\uffff\1\42\4\uffff\1\42\34\uffff\1\42\11\uffff"+
			"\1\42\15\uffff\1\42\14\uffff\1\42\1\1\2\42\1\uffff\2\42\1\uffff\1\1\3"+
			"\42\6\uffff\2\42\2\uffff\1\42",
			"\1\42\1\uffff\2\42\30\uffff\1\42\22\uffff\2\42\5\uffff\1\42\12\uffff"+
			"\1\42\22\uffff\1\42\2\uffff\1\42\4\uffff\1\42\34\uffff\1\42\11\uffff"+
			"\1\42\15\uffff\1\42\14\uffff\1\42\1\1\2\42\1\uffff\2\42\1\uffff\1\1\3"+
			"\42\6\uffff\2\42\2\uffff\1\42",
			"\1\42\1\uffff\2\42\30\uffff\1\42\22\uffff\2\42\5\uffff\1\42\12\uffff"+
			"\1\42\22\uffff\1\42\2\uffff\1\42\4\uffff\1\42\34\uffff\1\42\11\uffff"+
			"\1\42\15\uffff\1\42\14\uffff\1\42\1\1\2\42\1\uffff\2\42\1\uffff\1\1\3"+
			"\42\6\uffff\2\42\2\uffff\1\42",
			"\1\42\1\uffff\2\42\30\uffff\1\42\22\uffff\2\42\5\uffff\1\42\12\uffff"+
			"\1\42\22\uffff\1\42\2\uffff\1\42\4\uffff\1\42\34\uffff\1\42\11\uffff"+
			"\1\42\15\uffff\1\42\14\uffff\1\42\1\1\2\42\1\uffff\2\42\1\uffff\1\1\3"+
			"\42\6\uffff\2\42\2\uffff\1\42",
			"\1\42\1\uffff\2\42\30\uffff\1\42\22\uffff\2\42\5\uffff\1\42\12\uffff"+
			"\1\42\22\uffff\1\42\2\uffff\1\42\4\uffff\1\42\34\uffff\1\42\11\uffff"+
			"\1\42\15\uffff\1\42\14\uffff\1\42\1\1\2\42\1\uffff\2\42\1\uffff\1\1\3"+
			"\42\6\uffff\2\42\2\uffff\1\42",
			"\1\42\1\uffff\2\42\30\uffff\1\42\22\uffff\2\42\5\uffff\1\42\12\uffff"+
			"\1\42\22\uffff\1\42\2\uffff\1\42\4\uffff\1\42\34\uffff\1\42\11\uffff"+
			"\1\42\15\uffff\1\42\14\uffff\1\42\1\1\2\42\1\uffff\2\42\1\uffff\1\1\3"+
			"\42\6\uffff\2\42\2\uffff\1\42",
			"\1\42\1\uffff\2\42\30\uffff\1\42\22\uffff\2\42\5\uffff\1\42\12\uffff"+
			"\1\42\22\uffff\1\42\2\uffff\1\42\4\uffff\1\42\34\uffff\1\42\11\uffff"+
			"\1\42\15\uffff\1\42\14\uffff\1\42\1\1\2\42\1\uffff\2\42\1\uffff\1\1\3"+
			"\42\6\uffff\2\42\2\uffff\1\42",
			"\1\42\1\uffff\2\42\30\uffff\1\42\22\uffff\2\42\5\uffff\1\42\12\uffff"+
			"\1\42\22\uffff\1\42\2\uffff\1\42\4\uffff\1\42\34\uffff\1\42\11\uffff"+
			"\1\42\15\uffff\1\42\14\uffff\1\42\1\1\2\42\1\uffff\2\42\1\uffff\1\1\3"+
			"\42\6\uffff\2\42\2\uffff\1\42",
			"\1\42\1\uffff\2\42\30\uffff\1\42\22\uffff\2\42\5\uffff\1\42\12\uffff"+
			"\1\42\22\uffff\1\42\2\uffff\1\42\4\uffff\1\42\34\uffff\1\42\11\uffff"+
			"\1\42\15\uffff\1\42\14\uffff\1\42\1\1\2\42\1\uffff\2\42\1\uffff\1\1\3"+
			"\42\6\uffff\2\42\2\uffff\1\42",
			"\1\42\1\uffff\2\42\30\uffff\1\42\22\uffff\2\42\5\uffff\1\42\12\uffff"+
			"\1\42\22\uffff\1\42\2\uffff\1\42\4\uffff\1\42\34\uffff\1\42\11\uffff"+
			"\1\42\15\uffff\1\42\14\uffff\1\42\1\1\2\42\1\uffff\2\42\1\uffff\1\1\3"+
			"\42\6\uffff\2\42\2\uffff\1\42",
			"\1\42\1\uffff\2\42\30\uffff\1\42\22\uffff\2\42\5\uffff\1\42\12\uffff"+
			"\1\42\22\uffff\1\42\2\uffff\1\42\4\uffff\1\42\34\uffff\1\42\11\uffff"+
			"\1\42\15\uffff\1\42\14\uffff\1\42\1\1\2\42\1\uffff\2\42\1\uffff\1\1\3"+
			"\42\6\uffff\2\42\2\uffff\1\42",
			"\1\42\1\uffff\2\42\30\uffff\1\42\22\uffff\2\42\5\uffff\1\42\12\uffff"+
			"\1\42\22\uffff\1\42\2\uffff\1\42\4\uffff\1\42\34\uffff\1\42\11\uffff"+
			"\1\42\15\uffff\1\42\14\uffff\1\42\1\1\2\42\1\uffff\2\42\1\uffff\1\1\3"+
			"\42\6\uffff\2\42\2\uffff\1\42",
			"\1\42\1\uffff\2\42\30\uffff\1\42\22\uffff\2\42\5\uffff\1\42\12\uffff"+
			"\1\42\22\uffff\1\42\2\uffff\1\42\4\uffff\1\42\34\uffff\1\42\11\uffff"+
			"\1\42\15\uffff\1\42\14\uffff\1\42\1\1\2\42\1\uffff\2\42\1\uffff\1\1\3"+
			"\42\6\uffff\2\42\2\uffff\1\42",
			"\1\42\1\uffff\2\42\30\uffff\1\42\22\uffff\2\42\5\uffff\1\42\12\uffff"+
			"\1\42\22\uffff\1\42\2\uffff\1\42\4\uffff\1\42\34\uffff\1\42\11\uffff"+
			"\1\42\15\uffff\1\42\14\uffff\1\42\1\1\2\42\1\uffff\2\42\1\uffff\1\1\3"+
			"\42\6\uffff\2\42\2\uffff\1\42",
			"\1\42\1\uffff\2\42\30\uffff\1\42\22\uffff\2\42\5\uffff\1\42\12\uffff"+
			"\1\42\22\uffff\1\42\2\uffff\1\42\4\uffff\1\42\34\uffff\1\42\11\uffff"+
			"\1\42\15\uffff\1\42\14\uffff\1\42\1\uffff\2\42\1\uffff\2\42\1\uffff\1"+
			"\1\3\42\6\uffff\2\42\2\uffff\1\42"
	};

	static final short[] DFA202_eot = DFA.unpackEncodedString(DFA202_eotS);
	static final short[] DFA202_eof = DFA.unpackEncodedString(DFA202_eofS);
	static final char[] DFA202_min = DFA.unpackEncodedStringToUnsignedChars(DFA202_minS);
	static final char[] DFA202_max = DFA.unpackEncodedStringToUnsignedChars(DFA202_maxS);
	static final short[] DFA202_accept = DFA.unpackEncodedString(DFA202_acceptS);
	static final short[] DFA202_special = DFA.unpackEncodedString(DFA202_specialS);
	static final short[][] DFA202_transition;

	static {
		int numStates = DFA202_transitionS.length;
		DFA202_transition = new short[numStates][];
		for (int i=0; i<numStates; i++) {
			DFA202_transition[i] = DFA.unpackEncodedString(DFA202_transitionS[i]);
		}
	}

	protected class DFA202 extends DFA {

		public DFA202(BaseRecognizer recognizer) {
			this.recognizer = recognizer;
			this.decisionNumber = 202;
			this.eot = DFA202_eot;
			this.eof = DFA202_eof;
			this.min = DFA202_min;
			this.max = DFA202_max;
			this.accept = DFA202_accept;
			this.special = DFA202_special;
			this.transition = DFA202_transition;
		}
		@Override
		public String getDescription() {
			return "1525:1: simpleTerm returns [Term.Raw term] : (v= value |f= function | '(' c= comparatorType ')' t= simpleTerm );";
		}
	}

	static final String DFA205_eotS =
		"\37\uffff";
	static final String DFA205_eofS =
		"\37\uffff";
	static final String DFA205_minS =
		"\1\6\1\uffff\33\30\2\uffff";
	static final String DFA205_maxS =
		"\1\u00d2\1\uffff\32\u00c5\1\u00c3\2\uffff";
	static final String DFA205_acceptS =
		"\1\uffff\1\1\33\uffff\1\2\1\3";
	static final String DFA205_specialS =
		"\37\uffff}>";
	static final String[] DFA205_transitionS = {
			"\1\1\4\uffff\1\1\2\uffff\1\34\2\uffff\1\1\3\uffff\1\1\1\uffff\1\2\1\1"+
			"\4\uffff\2\4\4\uffff\1\4\1\uffff\1\5\3\uffff\1\6\1\7\1\10\1\uffff\1\4"+
			"\1\33\1\4\1\uffff\2\4\1\32\1\11\1\uffff\1\4\1\uffff\1\30\1\12\4\uffff"+
			"\1\33\1\13\1\uffff\1\14\2\uffff\3\4\1\15\1\uffff\1\4\1\uffff\2\4\1\uffff"+
			"\1\4\3\uffff\1\16\2\4\1\uffff\1\17\2\uffff\2\33\1\4\1\uffff\3\4\1\uffff"+
			"\3\4\4\uffff\2\1\1\4\1\uffff\1\4\1\uffff\1\1\2\uffff\1\4\2\uffff\5\4"+
			"\2\1\3\uffff\1\4\1\uffff\2\4\2\uffff\1\4\1\20\4\4\1\21\1\31\1\22\1\27"+
			"\1\23\1\uffff\1\1\1\4\1\uffff\1\33\2\4\4\uffff\2\4\1\uffff\1\24\1\4\1"+
			"\25\1\26\3\uffff\1\33\10\uffff\1\1\1\3\3\uffff\1\1\2\uffff\1\1\10\uffff"+
			"\1\1\4\uffff\1\1\3\uffff\1\1\6\uffff\1\1\3\uffff\1\1",
			"",
			"\1\36\u00a5\uffff\1\1\1\uffff\1\35\2\uffff\1\35\1\uffff\1\1",
			"\1\36\u00a5\uffff\1\1\1\uffff\1\35\2\uffff\1\35\1\uffff\1\1",
			"\1\36\u00a5\uffff\1\1\1\uffff\1\35\2\uffff\1\35\1\uffff\1\1",
			"\1\36\u00a5\uffff\1\1\1\uffff\1\35\2\uffff\1\35\1\uffff\1\1",
			"\1\36\u00a5\uffff\1\1\1\uffff\1\35\2\uffff\1\35\1\uffff\1\1",
			"\1\36\u00a5\uffff\1\1\1\uffff\1\35\2\uffff\1\35\1\uffff\1\1",
			"\1\36\u00a5\uffff\1\1\1\uffff\1\35\2\uffff\1\35\1\uffff\1\1",
			"\1\36\u00a5\uffff\1\1\1\uffff\1\35\2\uffff\1\35\1\uffff\1\1",
			"\1\36\u00a5\uffff\1\1\1\uffff\1\35\2\uffff\1\35\1\uffff\1\1",
			"\1\36\u00a5\uffff\1\1\1\uffff\1\35\2\uffff\1\35\1\uffff\1\1",
			"\1\36\u00a5\uffff\1\1\1\uffff\1\35\2\uffff\1\35\1\uffff\1\1",
			"\1\36\u00a5\uffff\1\1\1\uffff\1\35\2\uffff\1\35\1\uffff\1\1",
			"\1\36\u00a5\uffff\1\1\1\uffff\1\35\2\uffff\1\35\1\uffff\1\1",
			"\1\36\u00a5\uffff\1\1\1\uffff\1\35\2\uffff\1\35\1\uffff\1\1",
			"\1\36\u00a5\uffff\1\1\1\uffff\1\35\2\uffff\1\35\1\uffff\1\1",
			"\1\36\u00a5\uffff\1\1\1\uffff\1\35\2\uffff\1\35\1\uffff\1\1",
			"\1\36\u00a5\uffff\1\1\1\uffff\1\35\2\uffff\1\35\1\uffff\1\1",
			"\1\36\u00a5\uffff\1\1\1\uffff\1\35\2\uffff\1\35\1\uffff\1\1",
			"\1\36\u00a5\uffff\1\1\1\uffff\1\35\2\uffff\1\35\1\uffff\1\1",
			"\1\36\u00a5\uffff\1\1\1\uffff\1\35\2\uffff\1\35\1\uffff\1\1",
			"\1\36\u00a5\uffff\1\1\1\uffff\1\35\2\uffff\1\35\1\uffff\1\1",
			"\1\36\u00a5\uffff\1\1\1\uffff\1\35\2\uffff\1\35\1\uffff\1\1",
			"\1\36\u00a5\uffff\1\1\1\uffff\1\35\2\uffff\1\35\1\uffff\1\1",
			"\1\36\u00a5\uffff\1\1\1\uffff\1\35\2\uffff\1\35\1\uffff\1\1",
			"\1\36\u00a5\uffff\1\1\1\uffff\1\35\2\uffff\1\35\1\uffff\1\1",
			"\1\36\u00a7\uffff\1\35\2\uffff\1\35\1\uffff\1\1",
			"\1\36\u00a7\uffff\1\35\2\uffff\1\35",
			"",
			""
	};

	static final short[] DFA205_eot = DFA.unpackEncodedString(DFA205_eotS);
	static final short[] DFA205_eof = DFA.unpackEncodedString(DFA205_eofS);
	static final char[] DFA205_min = DFA.unpackEncodedStringToUnsignedChars(DFA205_minS);
	static final char[] DFA205_max = DFA.unpackEncodedStringToUnsignedChars(DFA205_maxS);
	static final short[] DFA205_accept = DFA.unpackEncodedString(DFA205_acceptS);
	static final short[] DFA205_special = DFA.unpackEncodedString(DFA205_specialS);
	static final short[][] DFA205_transition;

	static {
		int numStates = DFA205_transitionS.length;
		DFA205_transition = new short[numStates][];
		for (int i=0; i<numStates; i++) {
			DFA205_transition[i] = DFA.unpackEncodedString(DFA205_transitionS[i]);
		}
	}

	protected class DFA205 extends DFA {

		public DFA205(BaseRecognizer recognizer) {
			this.recognizer = recognizer;
			this.decisionNumber = 205;
			this.eot = DFA205_eot;
			this.eof = DFA205_eof;
			this.min = DFA205_min;
			this.max = DFA205_max;
			this.accept = DFA205_accept;
			this.special = DFA205_special;
			this.transition = DFA205_transition;
		}
		@Override
		public String getDescription() {
			return "1542:1: normalColumnOperation[List<Pair<ColumnMetadata.Raw, Operation.RawUpdate>> operations, ColumnMetadata.Raw key] : (t= term ( '+' c= cident )? |c= cident sig= ( '+' | '-' ) t= term |c= cident i= INTEGER );";
		}
	}

	static final String DFA213_eotS =
		"\35\uffff";
	static final String DFA213_eofS =
		"\35\uffff";
	static final String DFA213_minS =
		"\1\27\31\u00cb\1\6\2\uffff";
	static final String DFA213_maxS =
		"\1\u00ae\31\u00cb\1\u00d2\2\uffff";
	static final String DFA213_acceptS =
		"\33\uffff\1\1\1\2";
	static final String DFA213_specialS =
		"\35\uffff}>";
	static final String[] DFA213_transitionS = {
			"\1\1\5\uffff\2\3\4\uffff\1\3\1\uffff\1\4\3\uffff\1\5\1\6\1\7\1\uffff"+
			"\1\3\1\31\1\3\1\uffff\2\3\1\31\1\10\1\uffff\1\3\1\uffff\1\27\1\11\4\uffff"+
			"\1\31\1\12\1\uffff\1\13\2\uffff\3\3\1\14\1\uffff\1\3\1\uffff\2\3\1\uffff"+
			"\1\3\3\uffff\1\15\2\3\1\uffff\1\16\2\uffff\2\31\1\3\1\uffff\3\3\1\uffff"+
			"\3\3\6\uffff\1\3\1\uffff\1\3\4\uffff\1\3\2\uffff\5\3\5\uffff\1\3\1\uffff"+
			"\2\3\2\uffff\1\3\1\17\4\3\1\20\1\30\1\21\1\26\1\22\2\uffff\1\3\1\uffff"+
			"\1\31\2\3\4\uffff\2\3\1\uffff\1\23\1\3\1\24\1\25\3\uffff\1\31\11\uffff"+
			"\1\2",
			"\1\32",
			"\1\32",
			"\1\32",
			"\1\32",
			"\1\32",
			"\1\32",
			"\1\32",
			"\1\32",
			"\1\32",
			"\1\32",
			"\1\32",
			"\1\32",
			"\1\32",
			"\1\32",
			"\1\32",
			"\1\32",
			"\1\32",
			"\1\32",
			"\1\32",
			"\1\32",
			"\1\32",
			"\1\32",
			"\1\32",
			"\1\32",
			"\1\32",
			"\1\33\4\uffff\1\33\5\uffff\1\33\3\uffff\1\33\2\uffff\1\33\4\uffff\2"+
			"\33\4\uffff\1\33\1\uffff\1\33\3\uffff\3\33\1\uffff\3\33\1\uffff\4\33"+
			"\1\uffff\1\33\1\uffff\2\33\4\uffff\2\33\1\uffff\1\33\2\uffff\4\33\1\uffff"+
			"\1\33\1\uffff\2\33\1\uffff\1\33\3\uffff\3\33\1\uffff\1\33\2\uffff\3\33"+
			"\1\uffff\3\33\1\uffff\3\33\4\uffff\3\33\1\uffff\1\33\4\uffff\1\33\2\uffff"+
			"\7\33\3\uffff\1\33\1\uffff\2\33\2\uffff\13\33\2\uffff\1\33\1\uffff\3"+
			"\33\4\uffff\2\33\1\uffff\4\33\3\uffff\1\33\15\uffff\1\33\2\uffff\1\33"+
			"\34\uffff\1\34",
			"",
			""
	};

	static final short[] DFA213_eot = DFA.unpackEncodedString(DFA213_eotS);
	static final short[] DFA213_eof = DFA.unpackEncodedString(DFA213_eofS);
	static final char[] DFA213_min = DFA.unpackEncodedStringToUnsignedChars(DFA213_minS);
	static final char[] DFA213_max = DFA.unpackEncodedStringToUnsignedChars(DFA213_maxS);
	static final short[] DFA213_accept = DFA.unpackEncodedString(DFA213_acceptS);
	static final short[] DFA213_special = DFA.unpackEncodedString(DFA213_specialS);
	static final short[][] DFA213_transition;

	static {
		int numStates = DFA213_transitionS.length;
		DFA213_transition = new short[numStates][];
		for (int i=0; i<numStates; i++) {
			DFA213_transition[i] = DFA.unpackEncodedString(DFA213_transitionS[i]);
		}
	}

	protected class DFA213 extends DFA {

		public DFA213(BaseRecognizer recognizer) {
			this.recognizer = recognizer;
			this.decisionNumber = 213;
			this.eot = DFA213_eot;
			this.eof = DFA213_eof;
			this.min = DFA213_min;
			this.max = DFA213_max;
			this.accept = DFA213_accept;
			this.special = DFA213_special;
			this.transition = DFA213_transition;
		}
		@Override
		public String getDescription() {
			return "1622:1: property[PropertyDefinitions props] : (k= noncol_ident '=' simple= propertyValue |k= noncol_ident '=' map= fullMapLiteral );";
		}
	}

	static final String DFA218_eotS =
		"\101\uffff";
	static final String DFA218_eofS =
		"\101\uffff";
	static final String DFA218_minS =
		"\1\16\32\62\1\uffff\1\16\3\uffff\1\u00ad\2\uffff\32\62\4\uffff";
	static final String DFA218_maxS =
		"\1\u00be\32\u00ce\1\uffff\1\u00be\3\uffff\1\u00c7\2\uffff\32\u00ce\4\uffff";
	static final String DFA218_acceptS =
		"\33\uffff\1\4\1\uffff\1\1\1\2\1\3\1\uffff\1\7\1\10\32\uffff\1\12\1\5\1"+
		"\6\1\11";
	static final String DFA218_specialS =
		"\101\uffff}>";
	static final String[] DFA218_transitionS = {
			"\1\1\10\uffff\1\2\5\uffff\2\4\4\uffff\1\4\1\uffff\1\5\3\uffff\1\6\1\7"+
			"\1\10\1\uffff\1\4\1\32\1\4\1\uffff\2\4\1\32\1\11\1\uffff\1\4\1\uffff"+
			"\1\30\1\12\4\uffff\1\32\1\13\1\uffff\1\14\2\uffff\3\4\1\15\1\uffff\1"+
			"\4\1\uffff\2\4\1\uffff\1\4\3\uffff\1\16\2\4\1\uffff\1\17\2\uffff\2\32"+
			"\1\4\1\uffff\3\4\1\uffff\3\4\6\uffff\1\4\1\uffff\1\4\4\uffff\1\4\2\uffff"+
			"\5\4\5\uffff\1\4\1\uffff\2\4\2\uffff\1\4\1\20\4\4\1\21\1\31\1\22\1\27"+
			"\1\23\1\uffff\1\33\1\4\1\uffff\1\32\2\4\4\uffff\2\4\1\uffff\1\24\1\4"+
			"\1\25\1\26\3\uffff\1\32\11\uffff\1\3\17\uffff\1\34",
			"\1\41\35\uffff\1\40\7\uffff\1\37\6\uffff\1\36\134\uffff\1\35\14\uffff"+
			"\5\35\1\42",
			"\1\41\35\uffff\1\40\7\uffff\1\37\6\uffff\1\36\134\uffff\1\35\14\uffff"+
			"\5\35\1\42",
			"\1\41\35\uffff\1\40\7\uffff\1\37\6\uffff\1\36\134\uffff\1\35\14\uffff"+
			"\5\35\1\42",
			"\1\41\35\uffff\1\40\7\uffff\1\37\6\uffff\1\36\134\uffff\1\35\14\uffff"+
			"\5\35\1\42",
			"\1\41\35\uffff\1\40\7\uffff\1\37\6\uffff\1\36\134\uffff\1\35\14\uffff"+
			"\5\35\1\42",
			"\1\41\35\uffff\1\40\7\uffff\1\37\6\uffff\1\36\134\uffff\1\35\14\uffff"+
			"\5\35\1\42",
			"\1\41\35\uffff\1\40\7\uffff\1\37\6\uffff\1\36\134\uffff\1\35\14\uffff"+
			"\5\35\1\42",
			"\1\41\35\uffff\1\40\7\uffff\1\37\6\uffff\1\36\134\uffff\1\35\14\uffff"+
			"\5\35\1\42",
			"\1\41\35\uffff\1\40\7\uffff\1\37\6\uffff\1\36\134\uffff\1\35\14\uffff"+
			"\5\35\1\42",
			"\1\41\35\uffff\1\40\7\uffff\1\37\6\uffff\1\36\134\uffff\1\35\14\uffff"+
			"\5\35\1\42",
			"\1\41\35\uffff\1\40\7\uffff\1\37\6\uffff\1\36\134\uffff\1\35\14\uffff"+
			"\5\35\1\42",
			"\1\41\35\uffff\1\40\7\uffff\1\37\6\uffff\1\36\134\uffff\1\35\14\uffff"+
			"\5\35\1\42",
			"\1\41\35\uffff\1\40\7\uffff\1\37\6\uffff\1\36\134\uffff\1\35\14\uffff"+
			"\5\35\1\42",
			"\1\41\35\uffff\1\40\7\uffff\1\37\6\uffff\1\36\134\uffff\1\35\14\uffff"+
			"\5\35\1\42",
			"\1\41\35\uffff\1\40\7\uffff\1\37\6\uffff\1\36\134\uffff\1\35\14\uffff"+
			"\5\35\1\42",
			"\1\41\35\uffff\1\40\7\uffff\1\37\6\uffff\1\36\134\uffff\1\35\14\uffff"+
			"\5\35\1\42",
			"\1\41\35\uffff\1\40\7\uffff\1\37\6\uffff\1\36\134\uffff\1\35\14\uffff"+
			"\5\35\1\42",
			"\1\41\35\uffff\1\40\7\uffff\1\37\6\uffff\1\36\134\uffff\1\35\14\uffff"+
			"\5\35\1\42",
			"\1\41\35\uffff\1\40\7\uffff\1\37\6\uffff\1\36\134\uffff\1\35\14\uffff"+
			"\5\35\1\42",
			"\1\41\35\uffff\1\40\7\uffff\1\37\6\uffff\1\36\134\uffff\1\35\14\uffff"+
			"\5\35\1\42",
			"\1\41\35\uffff\1\40\7\uffff\1\37\6\uffff\1\36\134\uffff\1\35\14\uffff"+
			"\5\35\1\42",
			"\1\41\35\uffff\1\40\7\uffff\1\37\6\uffff\1\36\134\uffff\1\35\14\uffff"+
			"\5\35\1\42",
			"\1\41\35\uffff\1\40\7\uffff\1\37\6\uffff\1\36\134\uffff\1\35\14\uffff"+
			"\5\35\1\42",
			"\1\41\35\uffff\1\40\7\uffff\1\37\6\uffff\1\36\134\uffff\1\35\14\uffff"+
			"\5\35\1\42",
			"\1\41\35\uffff\1\40\7\uffff\1\37\6\uffff\1\36\134\uffff\1\35\14\uffff"+
			"\5\35\1\42",
			"\1\41\35\uffff\1\40\7\uffff\1\37\6\uffff\1\36\134\uffff\1\35\14\uffff"+
			"\5\35\1\42",
			"",
			"\1\43\10\uffff\1\44\5\uffff\2\46\4\uffff\1\46\1\uffff\1\47\3\uffff\1"+
			"\50\1\51\1\52\1\uffff\1\46\1\74\1\46\1\uffff\2\46\1\74\1\53\1\uffff\1"+
			"\46\1\uffff\1\72\1\54\4\uffff\1\74\1\55\1\uffff\1\56\2\uffff\3\46\1\57"+
			"\1\uffff\1\46\1\uffff\2\46\1\uffff\1\46\3\uffff\1\60\2\46\1\uffff\1\61"+
			"\2\uffff\2\74\1\46\1\uffff\3\46\1\uffff\3\46\6\uffff\1\46\1\uffff\1\46"+
			"\4\uffff\1\46\2\uffff\5\46\5\uffff\1\46\1\uffff\2\46\2\uffff\1\46\1\62"+
			"\4\46\1\63\1\73\1\64\1\71\1\65\1\uffff\1\75\1\46\1\uffff\1\74\2\46\4"+
			"\uffff\2\46\1\uffff\1\66\1\46\1\67\1\70\3\uffff\1\74\11\uffff\1\45\17"+
			"\uffff\1\75",
			"",
			"",
			"",
			"\1\76\20\uffff\1\77\10\uffff\1\76",
			"",
			"",
			"\1\75\35\uffff\1\75\7\uffff\1\75\6\uffff\1\75\134\uffff\1\75\2\uffff"+
			"\1\100\2\uffff\1\100\6\uffff\6\75",
			"\1\75\35\uffff\1\75\7\uffff\1\75\6\uffff\1\75\134\uffff\1\75\2\uffff"+
			"\1\100\2\uffff\1\100\6\uffff\6\75",
			"\1\75\35\uffff\1\75\7\uffff\1\75\6\uffff\1\75\134\uffff\1\75\2\uffff"+
			"\1\100\2\uffff\1\100\6\uffff\6\75",
			"\1\75\35\uffff\1\75\7\uffff\1\75\6\uffff\1\75\134\uffff\1\75\2\uffff"+
			"\1\100\2\uffff\1\100\6\uffff\6\75",
			"\1\75\35\uffff\1\75\7\uffff\1\75\6\uffff\1\75\134\uffff\1\75\2\uffff"+
			"\1\100\2\uffff\1\100\6\uffff\6\75",
			"\1\75\35\uffff\1\75\7\uffff\1\75\6\uffff\1\75\134\uffff\1\75\2\uffff"+
			"\1\100\2\uffff\1\100\6\uffff\6\75",
			"\1\75\35\uffff\1\75\7\uffff\1\75\6\uffff\1\75\134\uffff\1\75\2\uffff"+
			"\1\100\2\uffff\1\100\6\uffff\6\75",
			"\1\75\35\uffff\1\75\7\uffff\1\75\6\uffff\1\75\134\uffff\1\75\2\uffff"+
			"\1\100\2\uffff\1\100\6\uffff\6\75",
			"\1\75\35\uffff\1\75\7\uffff\1\75\6\uffff\1\75\134\uffff\1\75\2\uffff"+
			"\1\100\2\uffff\1\100\6\uffff\6\75",
			"\1\75\35\uffff\1\75\7\uffff\1\75\6\uffff\1\75\134\uffff\1\75\2\uffff"+
			"\1\100\2\uffff\1\100\6\uffff\6\75",
			"\1\75\35\uffff\1\75\7\uffff\1\75\6\uffff\1\75\134\uffff\1\75\2\uffff"+
			"\1\100\2\uffff\1\100\6\uffff\6\75",
			"\1\75\35\uffff\1\75\7\uffff\1\75\6\uffff\1\75\134\uffff\1\75\2\uffff"+
			"\1\100\2\uffff\1\100\6\uffff\6\75",
			"\1\75\35\uffff\1\75\7\uffff\1\75\6\uffff\1\75\134\uffff\1\75\2\uffff"+
			"\1\100\2\uffff\1\100\6\uffff\6\75",
			"\1\75\35\uffff\1\75\7\uffff\1\75\6\uffff\1\75\134\uffff\1\75\2\uffff"+
			"\1\100\2\uffff\1\100\6\uffff\6\75",
			"\1\75\35\uffff\1\75\7\uffff\1\75\6\uffff\1\75\134\uffff\1\75\2\uffff"+
			"\1\100\2\uffff\1\100\6\uffff\6\75",
			"\1\75\35\uffff\1\75\7\uffff\1\75\6\uffff\1\75\134\uffff\1\75\2\uffff"+
			"\1\100\2\uffff\1\100\6\uffff\6\75",
			"\1\75\35\uffff\1\75\7\uffff\1\75\6\uffff\1\75\134\uffff\1\75\2\uffff"+
			"\1\100\2\uffff\1\100\6\uffff\6\75",
			"\1\75\35\uffff\1\75\7\uffff\1\75\6\uffff\1\75\134\uffff\1\75\2\uffff"+
			"\1\100\2\uffff\1\100\6\uffff\6\75",
			"\1\75\35\uffff\1\75\7\uffff\1\75\6\uffff\1\75\134\uffff\1\75\2\uffff"+
			"\1\100\2\uffff\1\100\6\uffff\6\75",
			"\1\75\35\uffff\1\75\7\uffff\1\75\6\uffff\1\75\134\uffff\1\75\2\uffff"+
			"\1\100\2\uffff\1\100\6\uffff\6\75",
			"\1\75\35\uffff\1\75\7\uffff\1\75\6\uffff\1\75\134\uffff\1\75\2\uffff"+
			"\1\100\2\uffff\1\100\6\uffff\6\75",
			"\1\75\35\uffff\1\75\7\uffff\1\75\6\uffff\1\75\134\uffff\1\75\2\uffff"+
			"\1\100\2\uffff\1\100\6\uffff\6\75",
			"\1\75\35\uffff\1\75\7\uffff\1\75\6\uffff\1\75\134\uffff\1\75\2\uffff"+
			"\1\100\2\uffff\1\100\6\uffff\6\75",
			"\1\75\35\uffff\1\75\7\uffff\1\75\6\uffff\1\75\134\uffff\1\75\2\uffff"+
			"\1\100\2\uffff\1\100\6\uffff\6\75",
			"\1\75\35\uffff\1\75\7\uffff\1\75\6\uffff\1\75\134\uffff\1\75\2\uffff"+
			"\1\100\2\uffff\1\100\6\uffff\6\75",
			"\1\75\35\uffff\1\75\7\uffff\1\75\6\uffff\1\75\134\uffff\1\75\2\uffff"+
			"\1\100\2\uffff\1\100\6\uffff\6\75",
			"",
			"",
			"",
			""
	};

	static final short[] DFA218_eot = DFA.unpackEncodedString(DFA218_eotS);
	static final short[] DFA218_eof = DFA.unpackEncodedString(DFA218_eofS);
	static final char[] DFA218_min = DFA.unpackEncodedStringToUnsignedChars(DFA218_minS);
	static final char[] DFA218_max = DFA.unpackEncodedStringToUnsignedChars(DFA218_maxS);
	static final short[] DFA218_accept = DFA.unpackEncodedString(DFA218_acceptS);
	static final short[] DFA218_special = DFA.unpackEncodedString(DFA218_specialS);
	static final short[][] DFA218_transition;

	static {
		int numStates = DFA218_transitionS.length;
		DFA218_transition = new short[numStates][];
		for (int i=0; i<numStates; i++) {
			DFA218_transition[i] = DFA.unpackEncodedString(DFA218_transitionS[i]);
		}
	}

	protected class DFA218 extends DFA {

		public DFA218(BaseRecognizer recognizer) {
			this.recognizer = recognizer;
			this.decisionNumber = 218;
			this.eot = DFA218_eot;
			this.eof = DFA218_eof;
			this.min = DFA218_min;
			this.max = DFA218_max;
			this.accept = DFA218_accept;
			this.special = DFA218_special;
			this.transition = DFA218_transition;
		}
		@Override
		public String getDescription() {
			return "1641:1: relation[WhereClause.Builder clauses] : (name= cident type= relationType t= term |name= cident K_LIKE t= term |name= cident K_IS K_NOT K_NULL | K_TOKEN l= tupleOfIdentifiers type= relationType t= term |name= cident K_IN marker= inMarker |name= cident K_IN inValues= singleColumnInValues |name= cident rt= containsOperator t= term |name= cident '[' key= term ']' type= relationType t= term |ids= tupleOfIdentifiers ( K_IN ( '(' ')' |tupleInMarker= inMarkerForTuple |literals= tupleOfTupleLiterals |markers= tupleOfMarkersForTuples ) |type= relationType literal= tupleLiteral |type= relationType tupleMarker= markerForTuple ) | '(' relation[$clauses] ')' );";
		}
	}

	static final String DFA217_eotS =
		"\12\uffff";
	static final String DFA217_eofS =
		"\12\uffff";
	static final String DFA217_minS =
		"\1\120\1\uffff\6\u00ad\2\uffff";
	static final String DFA217_maxS =
		"\1\u00cd\1\uffff\6\u00c7\2\uffff";
	static final String DFA217_acceptS =
		"\1\uffff\1\1\6\uffff\1\2\1\3";
	static final String DFA217_specialS =
		"\12\uffff}>";
	static final String[] DFA217_transitionS = {
			"\1\1\153\uffff\1\7\14\uffff\1\3\1\4\1\2\1\5\1\6",
			"",
			"\1\11\20\uffff\1\10\10\uffff\1\11",
			"\1\11\20\uffff\1\10\10\uffff\1\11",
			"\1\11\20\uffff\1\10\10\uffff\1\11",
			"\1\11\20\uffff\1\10\10\uffff\1\11",
			"\1\11\20\uffff\1\10\10\uffff\1\11",
			"\1\11\20\uffff\1\10\10\uffff\1\11",
			"",
			""
	};

	static final short[] DFA217_eot = DFA.unpackEncodedString(DFA217_eotS);
	static final short[] DFA217_eof = DFA.unpackEncodedString(DFA217_eofS);
	static final char[] DFA217_min = DFA.unpackEncodedStringToUnsignedChars(DFA217_minS);
	static final char[] DFA217_max = DFA.unpackEncodedStringToUnsignedChars(DFA217_maxS);
	static final short[] DFA217_accept = DFA.unpackEncodedString(DFA217_acceptS);
	static final short[] DFA217_special = DFA.unpackEncodedString(DFA217_specialS);
	static final short[][] DFA217_transition;

	static {
		int numStates = DFA217_transitionS.length;
		DFA217_transition = new short[numStates][];
		for (int i=0; i<numStates; i++) {
			DFA217_transition[i] = DFA.unpackEncodedString(DFA217_transitionS[i]);
		}
	}

	protected class DFA217 extends DFA {

		public DFA217(BaseRecognizer recognizer) {
			this.recognizer = recognizer;
			this.decisionNumber = 217;
			this.eot = DFA217_eot;
			this.eof = DFA217_eof;
			this.min = DFA217_min;
			this.max = DFA217_max;
			this.accept = DFA217_accept;
			this.special = DFA217_special;
			this.transition = DFA217_transition;
		}
		@Override
		public String getDescription() {
			return "1654:7: ( K_IN ( '(' ')' |tupleInMarker= inMarkerForTuple |literals= tupleOfTupleLiterals |markers= tupleOfMarkersForTuples ) |type= relationType literal= tupleLiteral |type= relationType tupleMarker= markerForTuple )";
		}
	}

	static final String DFA228_eotS =
		"\40\uffff";
	static final String DFA228_eofS =
		"\1\uffff\25\35\2\32\1\uffff\1\32\1\uffff\1\32\4\uffff";
	static final String DFA228_minS =
		"\1\27\27\106\1\uffff\1\106\1\uffff\1\106\4\uffff";
	static final String DFA228_maxS =
		"\1\u00b2\27\u00cc\1\uffff\1\u00cc\1\uffff\1\u00cc\4\uffff";
	static final String DFA228_acceptS =
		"\30\uffff\1\2\1\uffff\1\4\1\uffff\1\6\1\1\1\3\1\5";
	static final String DFA228_specialS =
		"\40\uffff}>";
	static final String[] DFA228_transitionS = {
			"\1\32\5\uffff\2\32\4\uffff\1\32\1\uffff\1\1\3\uffff\1\2\1\3\1\4\1\uffff"+
			"\3\32\1\uffff\3\32\1\5\1\uffff\1\32\1\uffff\1\24\1\6\4\uffff\1\32\1\7"+
			"\1\uffff\1\10\2\uffff\3\32\1\11\1\uffff\1\33\1\uffff\2\32\1\uffff\1\32"+
			"\3\uffff\1\12\2\32\1\uffff\1\13\2\uffff\3\32\1\uffff\3\32\1\uffff\1\27"+
			"\1\32\1\26\6\uffff\1\32\1\uffff\1\32\4\uffff\1\32\2\uffff\5\32\5\uffff"+
			"\1\32\1\uffff\2\32\1\uffff\1\30\1\32\1\14\4\32\1\15\1\25\1\16\1\23\1"+
			"\17\2\uffff\1\32\1\uffff\1\32\1\31\1\32\4\uffff\2\32\1\uffff\1\20\1\32"+
			"\1\21\1\22\3\uffff\1\32\11\uffff\1\32\3\uffff\1\34",
			"\1\35\14\uffff\1\35\12\uffff\1\35\34\uffff\1\35\12\uffff\1\35\70\uffff"+
			"\1\35\2\uffff\1\35\2\uffff\1\32\2\uffff\1\35\3\uffff\1\35",
			"\1\35\14\uffff\1\35\12\uffff\1\35\34\uffff\1\35\12\uffff\1\35\70\uffff"+
			"\1\35\2\uffff\1\35\2\uffff\1\32\2\uffff\1\35\3\uffff\1\35",
			"\1\35\14\uffff\1\35\12\uffff\1\35\34\uffff\1\35\12\uffff\1\35\70\uffff"+
			"\1\35\2\uffff\1\35\2\uffff\1\32\2\uffff\1\35\3\uffff\1\35",
			"\1\35\14\uffff\1\35\12\uffff\1\35\34\uffff\1\35\12\uffff\1\35\70\uffff"+
			"\1\35\2\uffff\1\35\2\uffff\1\32\2\uffff\1\35\3\uffff\1\35",
			"\1\35\14\uffff\1\35\12\uffff\1\35\34\uffff\1\35\12\uffff\1\35\70\uffff"+
			"\1\35\2\uffff\1\35\2\uffff\1\32\2\uffff\1\35\3\uffff\1\35",
			"\1\35\14\uffff\1\35\12\uffff\1\35\34\uffff\1\35\12\uffff\1\35\70\uffff"+
			"\1\35\2\uffff\1\35\2\uffff\1\32\2\uffff\1\35\3\uffff\1\35",
			"\1\35\14\uffff\1\35\12\uffff\1\35\34\uffff\1\35\12\uffff\1\35\70\uffff"+
			"\1\35\2\uffff\1\35\2\uffff\1\32\2\uffff\1\35\3\uffff\1\35",
			"\1\35\14\uffff\1\35\12\uffff\1\35\34\uffff\1\35\12\uffff\1\35\70\uffff"+
			"\1\35\2\uffff\1\35\2\uffff\1\32\2\uffff\1\35\3\uffff\1\35",
			"\1\35\14\uffff\1\35\12\uffff\1\35\34\uffff\1\35\12\uffff\1\35\70\uffff"+
			"\1\35\2\uffff\1\35\2\uffff\1\32\2\uffff\1\35\3\uffff\1\35",
			"\1\35\14\uffff\1\35\12\uffff\1\35\34\uffff\1\35\12\uffff\1\35\70\uffff"+
			"\1\35\2\uffff\1\35\2\uffff\1\32\2\uffff\1\35\3\uffff\1\35",
			"\1\35\14\uffff\1\35\12\uffff\1\35\34\uffff\1\35\12\uffff\1\35\70\uffff"+
			"\1\35\2\uffff\1\35\2\uffff\1\32\2\uffff\1\35\3\uffff\1\35",
			"\1\35\14\uffff\1\35\12\uffff\1\35\34\uffff\1\35\12\uffff\1\35\70\uffff"+
			"\1\35\2\uffff\1\35\2\uffff\1\32\2\uffff\1\35\3\uffff\1\35",
			"\1\35\14\uffff\1\35\12\uffff\1\35\34\uffff\1\35\12\uffff\1\35\70\uffff"+
			"\1\35\2\uffff\1\35\2\uffff\1\32\2\uffff\1\35\3\uffff\1\35",
			"\1\35\14\uffff\1\35\12\uffff\1\35\34\uffff\1\35\12\uffff\1\35\70\uffff"+
			"\1\35\2\uffff\1\35\2\uffff\1\32\2\uffff\1\35\3\uffff\1\35",
			"\1\35\14\uffff\1\35\12\uffff\1\35\34\uffff\1\35\12\uffff\1\35\70\uffff"+
			"\1\35\2\uffff\1\35\2\uffff\1\32\2\uffff\1\35\3\uffff\1\35",
			"\1\35\14\uffff\1\35\12\uffff\1\35\34\uffff\1\35\12\uffff\1\35\70\uffff"+
			"\1\35\2\uffff\1\35\2\uffff\1\32\2\uffff\1\35\3\uffff\1\35",
			"\1\35\14\uffff\1\35\12\uffff\1\35\34\uffff\1\35\12\uffff\1\35\70\uffff"+
			"\1\35\2\uffff\1\35\2\uffff\1\32\2\uffff\1\35\3\uffff\1\35",
			"\1\35\14\uffff\1\35\12\uffff\1\35\34\uffff\1\35\12\uffff\1\35\70\uffff"+
			"\1\35\2\uffff\1\35\2\uffff\1\32\2\uffff\1\35\3\uffff\1\35",
			"\1\35\14\uffff\1\35\12\uffff\1\35\34\uffff\1\35\12\uffff\1\35\70\uffff"+
			"\1\35\2\uffff\1\35\2\uffff\1\32\2\uffff\1\35\3\uffff\1\35",
			"\1\35\14\uffff\1\35\12\uffff\1\35\34\uffff\1\35\12\uffff\1\35\70\uffff"+
			"\1\35\2\uffff\1\35\2\uffff\1\32\2\uffff\1\35\3\uffff\1\35",
			"\1\35\14\uffff\1\35\12\uffff\1\35\34\uffff\1\35\12\uffff\1\35\70\uffff"+
			"\1\35\2\uffff\1\35\2\uffff\1\32\2\uffff\1\35\3\uffff\1\35",
			"\1\32\14\uffff\1\32\12\uffff\1\32\34\uffff\1\32\12\uffff\1\32\70\uffff"+
			"\1\32\2\uffff\1\32\2\uffff\1\32\2\uffff\1\32\1\30\2\uffff\1\32",
			"\1\32\14\uffff\1\32\12\uffff\1\32\34\uffff\1\32\12\uffff\1\32\70\uffff"+
			"\1\32\2\uffff\1\32\2\uffff\1\32\2\uffff\1\32\1\30\2\uffff\1\32",
			"",
			"\1\32\14\uffff\1\32\12\uffff\1\32\34\uffff\1\32\12\uffff\1\32\70\uffff"+
			"\1\32\2\uffff\1\32\2\uffff\1\32\2\uffff\1\32\1\36\2\uffff\1\32",
			"",
			"\1\32\14\uffff\1\32\12\uffff\1\32\34\uffff\1\32\12\uffff\1\32\70\uffff"+
			"\1\32\2\uffff\1\32\2\uffff\1\32\2\uffff\1\32\1\37\2\uffff\1\32",
			"",
			"",
			"",
			""
	};

	static final short[] DFA228_eot = DFA.unpackEncodedString(DFA228_eotS);
	static final short[] DFA228_eof = DFA.unpackEncodedString(DFA228_eofS);
	static final char[] DFA228_min = DFA.unpackEncodedStringToUnsignedChars(DFA228_minS);
	static final char[] DFA228_max = DFA.unpackEncodedStringToUnsignedChars(DFA228_maxS);
	static final short[] DFA228_accept = DFA.unpackEncodedString(DFA228_acceptS);
	static final short[] DFA228_special = DFA.unpackEncodedString(DFA228_specialS);
	static final short[][] DFA228_transition;

	static {
		int numStates = DFA228_transitionS.length;
		DFA228_transition = new short[numStates][];
		for (int i=0; i<numStates; i++) {
			DFA228_transition[i] = DFA.unpackEncodedString(DFA228_transitionS[i]);
		}
	}

	protected class DFA228 extends DFA {

		public DFA228(BaseRecognizer recognizer) {
			this.recognizer = recognizer;
			this.decisionNumber = 228;
			this.eot = DFA228_eot;
			this.eof = DFA228_eof;
			this.min = DFA228_min;
			this.max = DFA228_max;
			this.accept = DFA228_accept;
			this.special = DFA228_special;
			this.transition = DFA228_transition;
		}
		@Override
		public String getDescription() {
			return "1715:1: comparatorType returns [CQL3Type.Raw t] : (n= native_type |c= collection_type |tt= tuple_type |id= userTypeName | K_FROZEN '<' f= comparatorType '>' |s= STRING_LITERAL );";
		}
	}

	public static final BitSet FOLLOW_selectStatement_in_cqlStatement59 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_insertStatement_in_cqlStatement88 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_updateStatement_in_cqlStatement117 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_batchStatement_in_cqlStatement146 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_deleteStatement_in_cqlStatement176 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_useStatement_in_cqlStatement205 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_truncateStatement_in_cqlStatement237 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_createKeyspaceStatement_in_cqlStatement264 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_createTableStatement_in_cqlStatement285 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_createIndexStatement_in_cqlStatement308 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_dropKeyspaceStatement_in_cqlStatement331 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_dropTableStatement_in_cqlStatement353 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_dropIndexStatement_in_cqlStatement378 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_alterTableStatement_in_cqlStatement403 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_alterKeyspaceStatement_in_cqlStatement427 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_grantPermissionsStatement_in_cqlStatement448 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_revokePermissionsStatement_in_cqlStatement466 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_listPermissionsStatement_in_cqlStatement483 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_createUserStatement_in_cqlStatement502 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_alterUserStatement_in_cqlStatement526 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_dropUserStatement_in_cqlStatement551 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_listUsersStatement_in_cqlStatement577 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_createTriggerStatement_in_cqlStatement602 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_dropTriggerStatement_in_cqlStatement623 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_createTypeStatement_in_cqlStatement646 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_alterTypeStatement_in_cqlStatement670 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_dropTypeStatement_in_cqlStatement695 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_createFunctionStatement_in_cqlStatement721 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_dropFunctionStatement_in_cqlStatement741 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_createAggregateStatement_in_cqlStatement763 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_dropAggregateStatement_in_cqlStatement782 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_createRoleStatement_in_cqlStatement803 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_alterRoleStatement_in_cqlStatement827 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_dropRoleStatement_in_cqlStatement852 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_listRolesStatement_in_cqlStatement878 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_grantRoleStatement_in_cqlStatement903 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_revokeRoleStatement_in_cqlStatement928 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_createMaterializedViewStatement_in_cqlStatement952 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_dropMaterializedViewStatement_in_cqlStatement964 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_alterMaterializedViewStatement_in_cqlStatement978 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_USE_in_useStatement1004 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00006011EC3A7FF3L});
	public static final BitSet FOLLOW_keyspaceName_in_useStatement1008 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_SELECT_in_selectStatement1042 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x000000000004C088L});
	public static final BitSet FOLLOW_K_JSON_in_selectStatement1068 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x000000000004C088L});
	public static final BitSet FOLLOW_selectClause_in_selectStatement1077 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000100L});
	public static final BitSet FOLLOW_K_FROM_in_selectStatement1085 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00006011EC3A7FF3L});
	public static final BitSet FOLLOW_columnFamilyName_in_selectStatement1089 = new BitSet(new long[]{0x0000000080000002L,0x0048000100004000L,0x0000000400000000L});
	public static final BitSet FOLLOW_K_WHERE_in_selectStatement1099 = new BitSet(new long[]{0xC35EEE2860804000L,0x41F2140EEE5C5AF2L,0x40004011EC3B7FF3L,0x0000000000020000L});
	public static final BitSet FOLLOW_whereClause_in_selectStatement1103 = new BitSet(new long[]{0x0000000080000002L,0x0048000100004000L});
	public static final BitSet FOLLOW_K_GROUP_in_selectStatement1116 = new BitSet(new long[]{0x0000100000000000L});
	public static final BitSet FOLLOW_K_BY_in_selectStatement1118 = new BitSet(new long[]{0xC35EEE2860804000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_groupByClause_in_selectStatement1120 = new BitSet(new long[]{0x0000000080000002L,0x0048000100000000L,0x0000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_194_in_selectStatement1125 = new BitSet(new long[]{0xC35EEE2860804000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_groupByClause_in_selectStatement1127 = new BitSet(new long[]{0x0000000080000002L,0x0048000100000000L,0x0000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_K_ORDER_in_selectStatement1144 = new BitSet(new long[]{0x0000100000000000L});
	public static final BitSet FOLLOW_K_BY_in_selectStatement1146 = new BitSet(new long[]{0xC35EEE2860804000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_orderByClause_in_selectStatement1148 = new BitSet(new long[]{0x0000000080000002L,0x0040000100000000L,0x0000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_194_in_selectStatement1153 = new BitSet(new long[]{0xC35EEE2860804000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_orderByClause_in_selectStatement1155 = new BitSet(new long[]{0x0000000080000002L,0x0040000100000000L,0x0000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_K_PER_in_selectStatement1172 = new BitSet(new long[]{0x0000000000000000L,0x0010000000000000L});
	public static final BitSet FOLLOW_K_PARTITION_in_selectStatement1174 = new BitSet(new long[]{0x0000000000000000L,0x0000000100000000L});
	public static final BitSet FOLLOW_K_LIMIT_in_selectStatement1176 = new BitSet(new long[]{0x0000000001000000L,0x0000000000000000L,0x0000200000000000L,0x0000000000000080L});
	public static final BitSet FOLLOW_intValue_in_selectStatement1180 = new BitSet(new long[]{0x0000000080000002L,0x0000000100000000L});
	public static final BitSet FOLLOW_K_LIMIT_in_selectStatement1195 = new BitSet(new long[]{0x0000000001000000L,0x0000000000000000L,0x0000200000000000L,0x0000000000000080L});
	public static final BitSet FOLLOW_intValue_in_selectStatement1199 = new BitSet(new long[]{0x0000000080000002L});
	public static final BitSet FOLLOW_K_ALLOW_in_selectStatement1214 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000020L});
	public static final BitSet FOLLOW_K_FILTERING_in_selectStatement1216 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_DISTINCT_in_selectClause1271 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x000000000004C088L});
	public static final BitSet FOLLOW_selectors_in_selectClause1275 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_selectors_in_selectClause1287 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_selector_in_selectors1312 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_194_in_selectors1317 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_selector_in_selectors1321 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_207_in_selectors1333 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_unaliasedSelector_in_selector1366 = new BitSet(new long[]{0x0000000800000002L});
	public static final BitSet FOLLOW_K_AS_in_selector1369 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_noncol_ident_in_selector1373 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_selectionAddition_in_unaliasedSelector1402 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_selectionMultiplication_in_selectionAddition1429 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000000000000009L});
	public static final BitSet FOLLOW_192_in_selectionAddition1445 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_selectionMultiplication_in_selectionAddition1449 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000000000000009L});
	public static final BitSet FOLLOW_195_in_selectionAddition1463 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_selectionMultiplication_in_selectionAddition1467 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000000000000009L});
	public static final BitSet FOLLOW_selectionGroup_in_selectionMultiplication1505 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x2000000000000000L,0x0000000000008040L});
	public static final BitSet FOLLOW_207_in_selectionMultiplication1521 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_selectionGroup_in_selectionMultiplication1525 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x2000000000000000L,0x0000000000008040L});
	public static final BitSet FOLLOW_198_in_selectionMultiplication1539 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_selectionGroup_in_selectionMultiplication1543 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x2000000000000000L,0x0000000000008040L});
	public static final BitSet FOLLOW_189_in_selectionMultiplication1557 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_selectionGroup_in_selectionMultiplication1561 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x2000000000000000L,0x0000000000008040L});
	public static final BitSet FOLLOW_selectionGroupWithField_in_selectionGroup1603 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_selectionGroupWithoutField_in_selectionGroup1615 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_195_in_selectionGroup1625 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_selectionGroup_in_selectionGroup1629 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_selectionGroupWithoutField_in_selectionGroupWithField1654 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000004020L});
	public static final BitSet FOLLOW_selectorModifier_in_selectionGroupWithField1658 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_fieldSelectorModifier_in_selectorModifier1685 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000004020L});
	public static final BitSet FOLLOW_selectorModifier_in_selectorModifier1690 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_206_in_selectorModifier1701 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40256011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_collectionSubSelection_in_selectorModifier1705 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000010000L});
	public static final BitSet FOLLOW_208_in_selectorModifier1708 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000004020L});
	public static final BitSet FOLLOW_selectorModifier_in_selectorModifier1712 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_197_in_fieldSelectorModifier1745 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_fident_in_fieldSelectorModifier1749 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_term_in_collectionSubSelection1787 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0001000000000000L});
	public static final BitSet FOLLOW_RANGE_in_collectionSubSelection1793 = new BitSet(new long[]{0xC35EEE2861A20842L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_term_in_collectionSubSelection1798 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_RANGE_in_collectionSubSelection1813 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_term_in_collectionSubSelection1819 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_simpleUnaliasedSelector_in_selectionGroupWithoutField1871 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_selectionTypeHint_in_selectionGroupWithoutField1889 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_selectionTupleOrNestedSelector_in_selectionGroupWithoutField1901 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_selectionList_in_selectionGroupWithoutField1913 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_selectionMapOrSet_in_selectionGroupWithoutField1925 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_190_in_selectionTypeHint1953 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00044011EC3A7FFBL});
	public static final BitSet FOLLOW_comparatorType_in_selectionTypeHint1957 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L});
	public static final BitSet FOLLOW_191_in_selectionTypeHint1959 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044080L});
	public static final BitSet FOLLOW_selectionGroupWithoutField_in_selectionTypeHint1963 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_206_in_selectionList2004 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000054088L});
	public static final BitSet FOLLOW_unaliasedSelector_in_selectionList2010 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000010004L});
	public static final BitSet FOLLOW_194_in_selectionList2016 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_unaliasedSelector_in_selectionList2020 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000010004L});
	public static final BitSet FOLLOW_208_in_selectionList2030 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_210_in_selectionMapOrSet2051 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_unaliasedSelector_in_selectionMapOrSet2055 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000080084L});
	public static final BitSet FOLLOW_selectionMap_in_selectionMapOrSet2061 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000080000L});
	public static final BitSet FOLLOW_selectionSet_in_selectionMapOrSet2070 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000080000L});
	public static final BitSet FOLLOW_211_in_selectionMapOrSet2076 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_210_in_selectionMapOrSet2084 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000080000L});
	public static final BitSet FOLLOW_211_in_selectionMapOrSet2086 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_199_in_selectionMap2131 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_unaliasedSelector_in_selectionMap2135 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_194_in_selectionMap2143 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_unaliasedSelector_in_selectionMap2147 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000000080L});
	public static final BitSet FOLLOW_199_in_selectionMap2149 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_unaliasedSelector_in_selectionMap2153 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_194_in_selectionSet2205 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_unaliasedSelector_in_selectionSet2209 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_190_in_selectionTupleOrNestedSelector2255 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_unaliasedSelector_in_selectionTupleOrNestedSelector2259 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_194_in_selectionTupleOrNestedSelector2264 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_unaliasedSelector_in_selectionTupleOrNestedSelector2268 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_191_in_selectionTupleOrNestedSelector2275 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_sident_in_simpleUnaliasedSelector2300 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_selectionLiteral_in_simpleUnaliasedSelector2346 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_selectionFunction_in_simpleUnaliasedSelector2382 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_COUNT_in_selectionFunction2428 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x4000000000000000L});
	public static final BitSet FOLLOW_190_in_selectionFunction2430 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000008000L});
	public static final BitSet FOLLOW_207_in_selectionFunction2432 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L});
	public static final BitSet FOLLOW_191_in_selectionFunction2434 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_WRITETIME_in_selectionFunction2465 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x4000000000000000L});
	public static final BitSet FOLLOW_190_in_selectionFunction2467 = new BitSet(new long[]{0xC35EEE2860804000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_cident_in_selectionFunction2471 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L});
	public static final BitSet FOLLOW_191_in_selectionFunction2473 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_TTL_in_selectionFunction2496 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x4000000000000000L});
	public static final BitSet FOLLOW_190_in_selectionFunction2504 = new BitSet(new long[]{0xC35EEE2860804000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_cident_in_selectionFunction2508 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L});
	public static final BitSet FOLLOW_191_in_selectionFunction2510 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_CAST_in_selectionFunction2533 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x4000000000000000L});
	public static final BitSet FOLLOW_190_in_selectionFunction2540 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_unaliasedSelector_in_selectionFunction2544 = new BitSet(new long[]{0x0000000800000000L});
	public static final BitSet FOLLOW_K_AS_in_selectionFunction2546 = new BitSet(new long[]{0x83100E2000000000L,0x0000000000440082L,0x00000001A0007C20L});
	public static final BitSet FOLLOW_native_type_in_selectionFunction2550 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L});
	public static final BitSet FOLLOW_191_in_selectionFunction2552 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_functionName_in_selectionFunction2564 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x4000000000000000L});
	public static final BitSet FOLLOW_selectionFunctionArgs_in_selectionFunction2568 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_constant_in_selectionLiteral2593 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_NULL_in_selectionLiteral2623 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_199_in_selectionLiteral2657 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_noncol_ident_in_selectionLiteral2661 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_QMARK_in_selectionLiteral2682 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_190_in_selectionFunctionArgs2738 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0xC0246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_unaliasedSelector_in_selectionFunctionArgs2743 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_194_in_selectionFunctionArgs2759 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_unaliasedSelector_in_selectionFunctionArgs2763 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_191_in_selectionFunctionArgs2778 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_IDENT_in_sident2801 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_QUOTED_NAME_in_sident2826 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_unreserved_keyword_in_sident2845 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_relationOrExpression_in_whereClause2876 = new BitSet(new long[]{0x0000000200000002L});
	public static final BitSet FOLLOW_K_AND_in_whereClause2880 = new BitSet(new long[]{0xC35EEE2860804000L,0x41F2140EEE5C5AF2L,0x40004011EC3B7FF3L,0x0000000000020000L});
	public static final BitSet FOLLOW_relationOrExpression_in_whereClause2882 = new BitSet(new long[]{0x0000000200000002L});
	public static final BitSet FOLLOW_relation_in_relationOrExpression2904 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_customIndexExpression_in_relationOrExpression2913 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_209_in_customIndexExpression2941 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00006011EC3A7FF3L});
	public static final BitSet FOLLOW_idxName_in_customIndexExpression2943 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_194_in_customIndexExpression2946 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_term_in_customIndexExpression2950 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L});
	public static final BitSet FOLLOW_191_in_customIndexExpression2952 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_cident_in_orderByClause2982 = new BitSet(new long[]{0x1000001000000002L});
	public static final BitSet FOLLOW_K_ASC_in_orderByClause2985 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_DESC_in_orderByClause2989 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_cident_in_groupByClause3015 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_INSERT_in_insertStatement3040 = new BitSet(new long[]{0x0000000000000000L,0x0000000000800000L});
	public static final BitSet FOLLOW_K_INTO_in_insertStatement3042 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00006011EC3A7FF3L});
	public static final BitSet FOLLOW_columnFamilyName_in_insertStatement3046 = new BitSet(new long[]{0x0000000000000000L,0x0000000002000000L,0x4000000000000000L});
	public static final BitSet FOLLOW_normalInsertStatement_in_insertStatement3060 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_JSON_in_insertStatement3075 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0004200000000000L,0x0000000000000080L});
	public static final BitSet FOLLOW_jsonInsertStatement_in_insertStatement3079 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_190_in_normalInsertStatement3115 = new BitSet(new long[]{0xC35EEE2860804000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_cident_in_normalInsertStatement3119 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_194_in_normalInsertStatement3126 = new BitSet(new long[]{0xC35EEE2860804000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_cident_in_normalInsertStatement3130 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_191_in_normalInsertStatement3137 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000040000000L});
	public static final BitSet FOLLOW_K_VALUES_in_normalInsertStatement3145 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x4000000000000000L});
	public static final BitSet FOLLOW_190_in_normalInsertStatement3153 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_term_in_normalInsertStatement3157 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_194_in_normalInsertStatement3163 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_term_in_normalInsertStatement3167 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_191_in_normalInsertStatement3174 = new BitSet(new long[]{0x0000000000000002L,0x0000000000008000L,0x0000000010000000L});
	public static final BitSet FOLLOW_K_IF_in_normalInsertStatement3184 = new BitSet(new long[]{0x0000000000000000L,0x0000200000000000L});
	public static final BitSet FOLLOW_K_NOT_in_normalInsertStatement3186 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000010L});
	public static final BitSet FOLLOW_K_EXISTS_in_normalInsertStatement3188 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000010000000L});
	public static final BitSet FOLLOW_usingClause_in_normalInsertStatement3203 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_jsonValue_in_jsonInsertStatement3249 = new BitSet(new long[]{0x0400000000000002L,0x0000000000008000L,0x0000000010000000L});
	public static final BitSet FOLLOW_K_DEFAULT_in_jsonInsertStatement3259 = new BitSet(new long[]{0x0000000000000000L,0x0000400000000000L,0x0000000000800000L});
	public static final BitSet FOLLOW_K_NULL_in_jsonInsertStatement3263 = new BitSet(new long[]{0x0000000000000002L,0x0000000000008000L,0x0000000010000000L});
	public static final BitSet FOLLOW_K_UNSET_in_jsonInsertStatement3271 = new BitSet(new long[]{0x0000000000000002L,0x0000000000008000L,0x0000000010000000L});
	public static final BitSet FOLLOW_K_IF_in_jsonInsertStatement3287 = new BitSet(new long[]{0x0000000000000000L,0x0000200000000000L});
	public static final BitSet FOLLOW_K_NOT_in_jsonInsertStatement3289 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000010L});
	public static final BitSet FOLLOW_K_EXISTS_in_jsonInsertStatement3291 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000010000000L});
	public static final BitSet FOLLOW_usingClause_in_jsonInsertStatement3306 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_STRING_LITERAL_in_jsonValue3341 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_199_in_jsonValue3351 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_noncol_ident_in_jsonValue3355 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_QMARK_in_jsonValue3369 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_USING_in_usingClause3400 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000081000L});
	public static final BitSet FOLLOW_usingClauseObjective_in_usingClause3402 = new BitSet(new long[]{0x0000000200000002L});
	public static final BitSet FOLLOW_K_AND_in_usingClause3407 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000081000L});
	public static final BitSet FOLLOW_usingClauseObjective_in_usingClause3409 = new BitSet(new long[]{0x0000000200000002L});
	public static final BitSet FOLLOW_K_TIMESTAMP_in_usingClauseObjective3431 = new BitSet(new long[]{0x0000000001000000L,0x0000000000000000L,0x0000200000000000L,0x0000000000000080L});
	public static final BitSet FOLLOW_intValue_in_usingClauseObjective3435 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_TTL_in_usingClauseObjective3445 = new BitSet(new long[]{0x0000000001000000L,0x0000000000000000L,0x0000200000000000L,0x0000000000000080L});
	public static final BitSet FOLLOW_intValue_in_usingClauseObjective3449 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_UPDATE_in_updateStatement3483 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00006011EC3A7FF3L});
	public static final BitSet FOLLOW_columnFamilyName_in_updateStatement3487 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000010000008L});
	public static final BitSet FOLLOW_usingClause_in_updateStatement3497 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000008L});
	public static final BitSet FOLLOW_K_SET_in_updateStatement3509 = new BitSet(new long[]{0xC35EEE2860804000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_columnOperation_in_updateStatement3511 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000400000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_194_in_updateStatement3515 = new BitSet(new long[]{0xC35EEE2860804000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_columnOperation_in_updateStatement3517 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000400000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_K_WHERE_in_updateStatement3528 = new BitSet(new long[]{0xC35EEE2860804000L,0x41F2140EEE5C5AF2L,0x40004011EC3B7FF3L,0x0000000000020000L});
	public static final BitSet FOLLOW_whereClause_in_updateStatement3532 = new BitSet(new long[]{0x0000000000000002L,0x0000000000008000L});
	public static final BitSet FOLLOW_K_IF_in_updateStatement3542 = new BitSet(new long[]{0xC35EEE2860804000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_K_EXISTS_in_updateStatement3546 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_updateConditions_in_updateStatement3554 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_columnCondition_in_updateConditions3596 = new BitSet(new long[]{0x0000000200000002L});
	public static final BitSet FOLLOW_K_AND_in_updateConditions3601 = new BitSet(new long[]{0xC35EEE2860804000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_columnCondition_in_updateConditions3603 = new BitSet(new long[]{0x0000000200000002L});
	public static final BitSet FOLLOW_K_DELETE_in_deleteStatement3640 = new BitSet(new long[]{0xC35EEE2860804000L,0x41F2140EEE5C5BF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_deleteSelection_in_deleteStatement3646 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000100L});
	public static final BitSet FOLLOW_K_FROM_in_deleteStatement3659 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00006011EC3A7FF3L});
	public static final BitSet FOLLOW_columnFamilyName_in_deleteStatement3663 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000410000000L});
	public static final BitSet FOLLOW_usingClauseDelete_in_deleteStatement3673 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000400000000L});
	public static final BitSet FOLLOW_K_WHERE_in_deleteStatement3685 = new BitSet(new long[]{0xC35EEE2860804000L,0x41F2140EEE5C5AF2L,0x40004011EC3B7FF3L,0x0000000000020000L});
	public static final BitSet FOLLOW_whereClause_in_deleteStatement3689 = new BitSet(new long[]{0x0000000000000002L,0x0000000000008000L});
	public static final BitSet FOLLOW_K_IF_in_deleteStatement3699 = new BitSet(new long[]{0xC35EEE2860804000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_K_EXISTS_in_deleteStatement3703 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_updateConditions_in_deleteStatement3711 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_deleteOp_in_deleteSelection3758 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_194_in_deleteSelection3773 = new BitSet(new long[]{0xC35EEE2860804000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_deleteOp_in_deleteSelection3777 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_cident_in_deleteOp3804 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_cident_in_deleteOp3831 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000004000L});
	public static final BitSet FOLLOW_206_in_deleteOp3833 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_term_in_deleteOp3837 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000010000L});
	public static final BitSet FOLLOW_208_in_deleteOp3839 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_cident_in_deleteOp3851 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000000020L});
	public static final BitSet FOLLOW_197_in_deleteOp3853 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_fident_in_deleteOp3857 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_USING_in_usingClauseDelete3877 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000001000L});
	public static final BitSet FOLLOW_K_TIMESTAMP_in_usingClauseDelete3879 = new BitSet(new long[]{0x0000000001000000L,0x0000000000000000L,0x0000200000000000L,0x0000000000000080L});
	public static final BitSet FOLLOW_intValue_in_usingClauseDelete3883 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_BEGIN_in_batchStatement3917 = new BitSet(new long[]{0x0010008000000000L,0x0000000000000000L,0x0000000000400000L});
	public static final BitSet FOLLOW_K_UNLOGGED_in_batchStatement3927 = new BitSet(new long[]{0x0000008000000000L});
	public static final BitSet FOLLOW_K_COUNTER_in_batchStatement3933 = new BitSet(new long[]{0x0000008000000000L});
	public static final BitSet FOLLOW_K_BATCH_in_batchStatement3946 = new BitSet(new long[]{0x0800000400000000L,0x0000000000200000L,0x0000000011000000L});
	public static final BitSet FOLLOW_usingClause_in_batchStatement3950 = new BitSet(new long[]{0x0800000400000000L,0x0000000000200000L,0x0000000001000000L});
	public static final BitSet FOLLOW_batchStatementObjective_in_batchStatement3970 = new BitSet(new long[]{0x0800000400000000L,0x0000000000200000L,0x0000000001000000L,0x0000000000000100L});
	public static final BitSet FOLLOW_200_in_batchStatement3972 = new BitSet(new long[]{0x0800000400000000L,0x0000000000200000L,0x0000000001000000L});
	public static final BitSet FOLLOW_K_APPLY_in_batchStatement3986 = new BitSet(new long[]{0x0000008000000000L});
	public static final BitSet FOLLOW_K_BATCH_in_batchStatement3988 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_insertStatement_in_batchStatementObjective4019 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_updateStatement_in_batchStatementObjective4032 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_deleteStatement_in_batchStatementObjective4045 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_CREATE_in_createAggregateStatement4078 = new BitSet(new long[]{0x0000000020000000L,0x0004000000000000L});
	public static final BitSet FOLLOW_K_OR_in_createAggregateStatement4081 = new BitSet(new long[]{0x0000000000000000L,0x2000000000000000L});
	public static final BitSet FOLLOW_K_REPLACE_in_createAggregateStatement4083 = new BitSet(new long[]{0x0000000020000000L});
	public static final BitSet FOLLOW_K_AGGREGATE_in_createAggregateStatement4095 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5CDAF2L,0x00006011EC3B7FF3L});
	public static final BitSet FOLLOW_K_IF_in_createAggregateStatement4104 = new BitSet(new long[]{0x0000000000000000L,0x0000200000000000L});
	public static final BitSet FOLLOW_K_NOT_in_createAggregateStatement4106 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000010L});
	public static final BitSet FOLLOW_K_EXISTS_in_createAggregateStatement4108 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00006011EC3B7FF3L});
	public static final BitSet FOLLOW_functionName_in_createAggregateStatement4122 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x4000000000000000L});
	public static final BitSet FOLLOW_190_in_createAggregateStatement4130 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x80044011EC3A7FFBL});
	public static final BitSet FOLLOW_comparatorType_in_createAggregateStatement4154 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_194_in_createAggregateStatement4170 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00044011EC3A7FFBL});
	public static final BitSet FOLLOW_comparatorType_in_createAggregateStatement4174 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_191_in_createAggregateStatement4198 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000010L});
	public static final BitSet FOLLOW_K_SFUNC_in_createAggregateStatement4206 = new BitSet(new long[]{0x835EAE2860800000L,0x41F2140EE85C5AF2L,0x00004001EC337FF3L});
	public static final BitSet FOLLOW_allowedFunctionName_in_createAggregateStatement4212 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000100L});
	public static final BitSet FOLLOW_K_STYPE_in_createAggregateStatement4220 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00044011EC3A7FFBL});
	public static final BitSet FOLLOW_comparatorType_in_createAggregateStatement4226 = new BitSet(new long[]{0x0000000000000002L,0x0000000000080040L});
	public static final BitSet FOLLOW_K_FINALFUNC_in_createAggregateStatement4244 = new BitSet(new long[]{0x835EAE2860800000L,0x41F2140EE85C5AF2L,0x00004001EC337FF3L});
	public static final BitSet FOLLOW_allowedFunctionName_in_createAggregateStatement4250 = new BitSet(new long[]{0x0000000000000002L,0x0000000000080000L});
	public static final BitSet FOLLOW_K_INITCOND_in_createAggregateStatement4277 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_term_in_createAggregateStatement4283 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_DROP_in_dropAggregateStatement4330 = new BitSet(new long[]{0x0000000020000000L});
	public static final BitSet FOLLOW_K_AGGREGATE_in_dropAggregateStatement4332 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5CDAF2L,0x00006011EC3B7FF3L});
	public static final BitSet FOLLOW_K_IF_in_dropAggregateStatement4341 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000010L});
	public static final BitSet FOLLOW_K_EXISTS_in_dropAggregateStatement4343 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00006011EC3B7FF3L});
	public static final BitSet FOLLOW_functionName_in_dropAggregateStatement4358 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x4000000000000000L});
	public static final BitSet FOLLOW_190_in_dropAggregateStatement4376 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x80044011EC3A7FFBL});
	public static final BitSet FOLLOW_comparatorType_in_dropAggregateStatement4404 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_194_in_dropAggregateStatement4422 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00044011EC3A7FFBL});
	public static final BitSet FOLLOW_comparatorType_in_dropAggregateStatement4426 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_191_in_dropAggregateStatement4454 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_CREATE_in_createFunctionStatement4511 = new BitSet(new long[]{0x0000000000000000L,0x0004000000000800L});
	public static final BitSet FOLLOW_K_OR_in_createFunctionStatement4514 = new BitSet(new long[]{0x0000000000000000L,0x2000000000000000L});
	public static final BitSet FOLLOW_K_REPLACE_in_createFunctionStatement4516 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000800L});
	public static final BitSet FOLLOW_K_FUNCTION_in_createFunctionStatement4528 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5CDAF2L,0x00006011EC3B7FF3L});
	public static final BitSet FOLLOW_K_IF_in_createFunctionStatement4537 = new BitSet(new long[]{0x0000000000000000L,0x0000200000000000L});
	public static final BitSet FOLLOW_K_NOT_in_createFunctionStatement4539 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000010L});
	public static final BitSet FOLLOW_K_EXISTS_in_createFunctionStatement4541 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00006011EC3B7FF3L});
	public static final BitSet FOLLOW_functionName_in_createFunctionStatement4555 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x4000000000000000L});
	public static final BitSet FOLLOW_190_in_createFunctionStatement4563 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x80004011EC3A7FF3L});
	public static final BitSet FOLLOW_noncol_ident_in_createFunctionStatement4587 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00044011EC3A7FFBL});
	public static final BitSet FOLLOW_comparatorType_in_createFunctionStatement4591 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_194_in_createFunctionStatement4607 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_noncol_ident_in_createFunctionStatement4611 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00044011EC3A7FFBL});
	public static final BitSet FOLLOW_comparatorType_in_createFunctionStatement4615 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_191_in_createFunctionStatement4639 = new BitSet(new long[]{0x0000200000000000L,0x4000000000000000L});
	public static final BitSet FOLLOW_K_RETURNS_in_createFunctionStatement4650 = new BitSet(new long[]{0x0000000000000000L,0x0000400000000000L});
	public static final BitSet FOLLOW_K_NULL_in_createFunctionStatement4652 = new BitSet(new long[]{0x0000000000000000L,0x0001000000000000L});
	public static final BitSet FOLLOW_K_CALLED_in_createFunctionStatement4658 = new BitSet(new long[]{0x0000000000000000L,0x0001000000000000L});
	public static final BitSet FOLLOW_K_ON_in_createFunctionStatement4664 = new BitSet(new long[]{0x0000000000000000L,0x0000400000000000L});
	public static final BitSet FOLLOW_K_NULL_in_createFunctionStatement4666 = new BitSet(new long[]{0x0000000000000000L,0x0000000000100000L});
	public static final BitSet FOLLOW_K_INPUT_in_createFunctionStatement4668 = new BitSet(new long[]{0x0000000000000000L,0x4000000000000000L});
	public static final BitSet FOLLOW_K_RETURNS_in_createFunctionStatement4676 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00044011EC3A7FFBL});
	public static final BitSet FOLLOW_comparatorType_in_createFunctionStatement4682 = new BitSet(new long[]{0x0000000000000000L,0x0000000040000000L});
	public static final BitSet FOLLOW_K_LANGUAGE_in_createFunctionStatement4690 = new BitSet(new long[]{0x0000000000800000L});
	public static final BitSet FOLLOW_IDENT_in_createFunctionStatement4696 = new BitSet(new long[]{0x0000000800000000L});
	public static final BitSet FOLLOW_K_AS_in_createFunctionStatement4704 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0004000000000000L});
	public static final BitSet FOLLOW_STRING_LITERAL_in_createFunctionStatement4710 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_DROP_in_dropFunctionStatement4748 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000800L});
	public static final BitSet FOLLOW_K_FUNCTION_in_dropFunctionStatement4750 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5CDAF2L,0x00006011EC3B7FF3L});
	public static final BitSet FOLLOW_K_IF_in_dropFunctionStatement4759 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000010L});
	public static final BitSet FOLLOW_K_EXISTS_in_dropFunctionStatement4761 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00006011EC3B7FF3L});
	public static final BitSet FOLLOW_functionName_in_dropFunctionStatement4776 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x4000000000000000L});
	public static final BitSet FOLLOW_190_in_dropFunctionStatement4794 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x80044011EC3A7FFBL});
	public static final BitSet FOLLOW_comparatorType_in_dropFunctionStatement4822 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_194_in_dropFunctionStatement4840 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00044011EC3A7FFBL});
	public static final BitSet FOLLOW_comparatorType_in_dropFunctionStatement4844 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_191_in_dropFunctionStatement4872 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_CREATE_in_createKeyspaceStatement4931 = new BitSet(new long[]{0x0000000000000000L,0x0000000010000000L});
	public static final BitSet FOLLOW_K_KEYSPACE_in_createKeyspaceStatement4933 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5CDAF2L,0x00006011EC3A7FF3L});
	public static final BitSet FOLLOW_K_IF_in_createKeyspaceStatement4936 = new BitSet(new long[]{0x0000000000000000L,0x0000200000000000L});
	public static final BitSet FOLLOW_K_NOT_in_createKeyspaceStatement4938 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000010L});
	public static final BitSet FOLLOW_K_EXISTS_in_createKeyspaceStatement4940 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00006011EC3A7FF3L});
	public static final BitSet FOLLOW_keyspaceName_in_createKeyspaceStatement4949 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000800000000L});
	public static final BitSet FOLLOW_K_WITH_in_createKeyspaceStatement4957 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_properties_in_createKeyspaceStatement4959 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_CREATE_in_createTableStatement4994 = new BitSet(new long[]{0x0001000000000000L});
	public static final BitSet FOLLOW_K_COLUMNFAMILY_in_createTableStatement4996 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5CDAF2L,0x00006011EC3A7FF3L});
	public static final BitSet FOLLOW_K_IF_in_createTableStatement4999 = new BitSet(new long[]{0x0000000000000000L,0x0000200000000000L});
	public static final BitSet FOLLOW_K_NOT_in_createTableStatement5001 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000010L});
	public static final BitSet FOLLOW_K_EXISTS_in_createTableStatement5003 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00006011EC3A7FF3L});
	public static final BitSet FOLLOW_columnFamilyName_in_createTableStatement5018 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x4000000000000000L});
	public static final BitSet FOLLOW_tableDefinition_in_createTableStatement5028 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_190_in_tableDefinition5047 = new BitSet(new long[]{0xC35EEE2860800000L,0x49F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_tableColumns_in_tableDefinition5049 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_194_in_tableDefinition5054 = new BitSet(new long[]{0xC35EEE2860800000L,0x49F2140EEE5C5AF2L,0x80004011EC3A7FF3L,0x0000000000000004L});
	public static final BitSet FOLLOW_tableColumns_in_tableDefinition5056 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_191_in_tableDefinition5063 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000800000000L});
	public static final BitSet FOLLOW_K_WITH_in_tableDefinition5073 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_tableProperty_in_tableDefinition5075 = new BitSet(new long[]{0x0000000200000002L});
	public static final BitSet FOLLOW_K_AND_in_tableDefinition5080 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_tableProperty_in_tableDefinition5082 = new BitSet(new long[]{0x0000000200000002L});
	public static final BitSet FOLLOW_ident_in_tableColumns5117 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00044011EC3A7FFBL});
	public static final BitSet FOLLOW_comparatorType_in_tableColumns5121 = new BitSet(new long[]{0x0000000000000002L,0x0800000000000000L,0x0000000000000040L});
	public static final BitSet FOLLOW_K_STATIC_in_tableColumns5124 = new BitSet(new long[]{0x0000000000000002L,0x0800000000000000L});
	public static final BitSet FOLLOW_K_PRIMARY_in_tableColumns5141 = new BitSet(new long[]{0x0000000000000000L,0x0000000004000000L});
	public static final BitSet FOLLOW_K_KEY_in_tableColumns5143 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_PRIMARY_in_tableColumns5155 = new BitSet(new long[]{0x0000000000000000L,0x0000000004000000L});
	public static final BitSet FOLLOW_K_KEY_in_tableColumns5157 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x4000000000000000L});
	public static final BitSet FOLLOW_190_in_tableColumns5159 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x40004011EC3A7FF3L});
	public static final BitSet FOLLOW_tablePartitionKey_in_tableColumns5161 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_194_in_tableColumns5165 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_ident_in_tableColumns5169 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_191_in_tableColumns5176 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ident_in_tablePartitionKey5213 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_190_in_tablePartitionKey5223 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_ident_in_tablePartitionKey5227 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_194_in_tablePartitionKey5233 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_ident_in_tablePartitionKey5237 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_191_in_tablePartitionKey5244 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_property_in_tableProperty5262 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_COMPACT_in_tableProperty5271 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000080L});
	public static final BitSet FOLLOW_K_STORAGE_in_tableProperty5273 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_CLUSTERING_in_tableProperty5283 = new BitSet(new long[]{0x0000000000000000L,0x0008000000000000L});
	public static final BitSet FOLLOW_K_ORDER_in_tableProperty5285 = new BitSet(new long[]{0x0000100000000000L});
	public static final BitSet FOLLOW_K_BY_in_tableProperty5287 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x4000000000000000L});
	public static final BitSet FOLLOW_190_in_tableProperty5289 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_tableClusteringOrder_in_tableProperty5291 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_194_in_tableProperty5295 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_tableClusteringOrder_in_tableProperty5297 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_191_in_tableProperty5302 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ident_in_tableClusteringOrder5330 = new BitSet(new long[]{0x1000001000000000L});
	public static final BitSet FOLLOW_K_ASC_in_tableClusteringOrder5333 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_DESC_in_tableClusteringOrder5337 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_CREATE_in_createTypeStatement5375 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000200000L});
	public static final BitSet FOLLOW_K_TYPE_in_createTypeStatement5377 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5CDAF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_K_IF_in_createTypeStatement5380 = new BitSet(new long[]{0x0000000000000000L,0x0000200000000000L});
	public static final BitSet FOLLOW_K_NOT_in_createTypeStatement5382 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000010L});
	public static final BitSet FOLLOW_K_EXISTS_in_createTypeStatement5384 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_userTypeName_in_createTypeStatement5402 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x4000000000000000L});
	public static final BitSet FOLLOW_190_in_createTypeStatement5415 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_typeColumns_in_createTypeStatement5417 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_194_in_createTypeStatement5422 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x80004011EC3A7FF3L,0x0000000000000004L});
	public static final BitSet FOLLOW_typeColumns_in_createTypeStatement5424 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_191_in_createTypeStatement5431 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_fident_in_typeColumns5451 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00044011EC3A7FFBL});
	public static final BitSet FOLLOW_comparatorType_in_typeColumns5455 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_CREATE_in_createIndexStatement5489 = new BitSet(new long[]{0x0040000000000000L,0x0000000000020000L});
	public static final BitSet FOLLOW_K_CUSTOM_in_createIndexStatement5492 = new BitSet(new long[]{0x0000000000000000L,0x0000000000020000L});
	public static final BitSet FOLLOW_K_INDEX_in_createIndexStatement5498 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F3140EEE5CDAF2L,0x00006011EC3A7FF3L});
	public static final BitSet FOLLOW_K_IF_in_createIndexStatement5501 = new BitSet(new long[]{0x0000000000000000L,0x0000200000000000L});
	public static final BitSet FOLLOW_K_NOT_in_createIndexStatement5503 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000010L});
	public static final BitSet FOLLOW_K_EXISTS_in_createIndexStatement5505 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F3140EEE5C5AF2L,0x00006011EC3A7FF3L});
	public static final BitSet FOLLOW_idxName_in_createIndexStatement5521 = new BitSet(new long[]{0x0000000000000000L,0x0001000000000000L});
	public static final BitSet FOLLOW_K_ON_in_createIndexStatement5526 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00006011EC3A7FF3L});
	public static final BitSet FOLLOW_columnFamilyName_in_createIndexStatement5530 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x4000000000000000L});
	public static final BitSet FOLLOW_190_in_createIndexStatement5532 = new BitSet(new long[]{0xC35EEE2860804000L,0x41F2140EEE5C5EF6L,0x80004011EC3A7FF3L});
	public static final BitSet FOLLOW_indexIdent_in_createIndexStatement5535 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_194_in_createIndexStatement5539 = new BitSet(new long[]{0xC35EEE2860804000L,0x41F2140EEE5C5EF6L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_indexIdent_in_createIndexStatement5541 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_191_in_createIndexStatement5548 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000810000000L});
	public static final BitSet FOLLOW_K_USING_in_createIndexStatement5559 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0004000000000000L});
	public static final BitSet FOLLOW_STRING_LITERAL_in_createIndexStatement5563 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000800000000L});
	public static final BitSet FOLLOW_K_WITH_in_createIndexStatement5578 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_properties_in_createIndexStatement5580 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_cident_in_indexIdent5612 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_VALUES_in_indexIdent5640 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x4000000000000000L});
	public static final BitSet FOLLOW_190_in_indexIdent5642 = new BitSet(new long[]{0xC35EEE2860804000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_cident_in_indexIdent5646 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L});
	public static final BitSet FOLLOW_191_in_indexIdent5648 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_KEYS_in_indexIdent5659 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x4000000000000000L});
	public static final BitSet FOLLOW_190_in_indexIdent5661 = new BitSet(new long[]{0xC35EEE2860804000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_cident_in_indexIdent5665 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L});
	public static final BitSet FOLLOW_191_in_indexIdent5667 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_ENTRIES_in_indexIdent5680 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x4000000000000000L});
	public static final BitSet FOLLOW_190_in_indexIdent5682 = new BitSet(new long[]{0xC35EEE2860804000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_cident_in_indexIdent5686 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L});
	public static final BitSet FOLLOW_191_in_indexIdent5688 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_FULL_in_indexIdent5698 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x4000000000000000L});
	public static final BitSet FOLLOW_190_in_indexIdent5700 = new BitSet(new long[]{0xC35EEE2860804000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_cident_in_indexIdent5704 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L});
	public static final BitSet FOLLOW_191_in_indexIdent5706 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_CREATE_in_createMaterializedViewStatement5743 = new BitSet(new long[]{0x0000000000000000L,0x0000001000000000L});
	public static final BitSet FOLLOW_K_MATERIALIZED_in_createMaterializedViewStatement5745 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000200000000L});
	public static final BitSet FOLLOW_K_VIEW_in_createMaterializedViewStatement5747 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5CDAF2L,0x00006011EC3A7FF3L});
	public static final BitSet FOLLOW_K_IF_in_createMaterializedViewStatement5750 = new BitSet(new long[]{0x0000000000000000L,0x0000200000000000L});
	public static final BitSet FOLLOW_K_NOT_in_createMaterializedViewStatement5752 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000010L});
	public static final BitSet FOLLOW_K_EXISTS_in_createMaterializedViewStatement5754 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00006011EC3A7FF3L});
	public static final BitSet FOLLOW_columnFamilyName_in_createMaterializedViewStatement5762 = new BitSet(new long[]{0x0000000800000000L});
	public static final BitSet FOLLOW_K_AS_in_createMaterializedViewStatement5764 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_K_SELECT_in_createMaterializedViewStatement5774 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x000000000004C088L});
	public static final BitSet FOLLOW_selectors_in_createMaterializedViewStatement5778 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000100L});
	public static final BitSet FOLLOW_K_FROM_in_createMaterializedViewStatement5780 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00006011EC3A7FF3L});
	public static final BitSet FOLLOW_columnFamilyName_in_createMaterializedViewStatement5784 = new BitSet(new long[]{0x0000000000000000L,0x0800000000000000L,0x0000000400000000L});
	public static final BitSet FOLLOW_K_WHERE_in_createMaterializedViewStatement5795 = new BitSet(new long[]{0xC35EEE2860804000L,0x41F2140EEE5C5AF2L,0x40004011EC3B7FF3L,0x0000000000020000L});
	public static final BitSet FOLLOW_whereClause_in_createMaterializedViewStatement5799 = new BitSet(new long[]{0x0000000000000000L,0x0800000000000000L});
	public static final BitSet FOLLOW_viewPrimaryKey_in_createMaterializedViewStatement5821 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000800000000L});
	public static final BitSet FOLLOW_K_WITH_in_createMaterializedViewStatement5834 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_viewProperty_in_createMaterializedViewStatement5836 = new BitSet(new long[]{0x0000000200000002L});
	public static final BitSet FOLLOW_K_AND_in_createMaterializedViewStatement5841 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_viewProperty_in_createMaterializedViewStatement5843 = new BitSet(new long[]{0x0000000200000002L});
	public static final BitSet FOLLOW_K_PRIMARY_in_viewPrimaryKey5867 = new BitSet(new long[]{0x0000000000000000L,0x0000000004000000L});
	public static final BitSet FOLLOW_K_KEY_in_viewPrimaryKey5869 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x4000000000000000L});
	public static final BitSet FOLLOW_190_in_viewPrimaryKey5871 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x40004011EC3A7FF3L});
	public static final BitSet FOLLOW_viewPartitionKey_in_viewPrimaryKey5873 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_194_in_viewPrimaryKey5877 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_ident_in_viewPrimaryKey5881 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_191_in_viewPrimaryKey5888 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ident_in_viewPartitionKey5925 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_190_in_viewPartitionKey5935 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_ident_in_viewPartitionKey5939 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_194_in_viewPartitionKey5945 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_ident_in_viewPartitionKey5949 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_191_in_viewPartitionKey5956 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_property_in_viewProperty5974 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_COMPACT_in_viewProperty5983 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000080L});
	public static final BitSet FOLLOW_K_STORAGE_in_viewProperty5985 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_CLUSTERING_in_viewProperty5995 = new BitSet(new long[]{0x0000000000000000L,0x0008000000000000L});
	public static final BitSet FOLLOW_K_ORDER_in_viewProperty5997 = new BitSet(new long[]{0x0000100000000000L});
	public static final BitSet FOLLOW_K_BY_in_viewProperty5999 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x4000000000000000L});
	public static final BitSet FOLLOW_190_in_viewProperty6001 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_viewClusteringOrder_in_viewProperty6003 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_194_in_viewProperty6007 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_viewClusteringOrder_in_viewProperty6009 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_191_in_viewProperty6014 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ident_in_viewClusteringOrder6042 = new BitSet(new long[]{0x1000001000000000L});
	public static final BitSet FOLLOW_K_ASC_in_viewClusteringOrder6045 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_DESC_in_viewClusteringOrder6049 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_CREATE_in_createTriggerStatement6087 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000020000L});
	public static final BitSet FOLLOW_K_TRIGGER_in_createTriggerStatement6089 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5CDAF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_K_IF_in_createTriggerStatement6092 = new BitSet(new long[]{0x0000000000000000L,0x0000200000000000L});
	public static final BitSet FOLLOW_K_NOT_in_createTriggerStatement6094 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000010L});
	public static final BitSet FOLLOW_K_EXISTS_in_createTriggerStatement6096 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_ident_in_createTriggerStatement6106 = new BitSet(new long[]{0x0000000000000000L,0x0001000000000000L});
	public static final BitSet FOLLOW_K_ON_in_createTriggerStatement6117 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00006011EC3A7FF3L});
	public static final BitSet FOLLOW_columnFamilyName_in_createTriggerStatement6121 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000010000000L});
	public static final BitSet FOLLOW_K_USING_in_createTriggerStatement6123 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0004000000000000L});
	public static final BitSet FOLLOW_STRING_LITERAL_in_createTriggerStatement6127 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_DROP_in_dropTriggerStatement6168 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000020000L});
	public static final BitSet FOLLOW_K_TRIGGER_in_dropTriggerStatement6170 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5CDAF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_K_IF_in_dropTriggerStatement6173 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000010L});
	public static final BitSet FOLLOW_K_EXISTS_in_dropTriggerStatement6175 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_ident_in_dropTriggerStatement6185 = new BitSet(new long[]{0x0000000000000000L,0x0001000000000000L});
	public static final BitSet FOLLOW_K_ON_in_dropTriggerStatement6188 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00006011EC3A7FF3L});
	public static final BitSet FOLLOW_columnFamilyName_in_dropTriggerStatement6192 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_ALTER_in_alterKeyspaceStatement6232 = new BitSet(new long[]{0x0000000000000000L,0x0000000010000000L});
	public static final BitSet FOLLOW_K_KEYSPACE_in_alterKeyspaceStatement6234 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00006011EC3A7FF3L});
	public static final BitSet FOLLOW_keyspaceName_in_alterKeyspaceStatement6238 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000800000000L});
	public static final BitSet FOLLOW_K_WITH_in_alterKeyspaceStatement6248 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_properties_in_alterKeyspaceStatement6250 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_ALTER_in_alterTableStatement6276 = new BitSet(new long[]{0x0001000000000000L});
	public static final BitSet FOLLOW_K_COLUMNFAMILY_in_alterTableStatement6278 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00006011EC3A7FF3L});
	public static final BitSet FOLLOW_columnFamilyName_in_alterTableStatement6282 = new BitSet(new long[]{0x0000000110000000L,0x1000000000000001L,0x0000000800000000L});
	public static final BitSet FOLLOW_K_ALTER_in_alterTableStatement6302 = new BitSet(new long[]{0xC35EEE2860804000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_cident_in_alterTableStatement6306 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000200000L});
	public static final BitSet FOLLOW_K_TYPE_in_alterTableStatement6308 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00044011EC3A7FFBL});
	public static final BitSet FOLLOW_comparatorType_in_alterTableStatement6312 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_ADD_in_alterTableStatement6325 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x40004011EC3A7FF3L});
	public static final BitSet FOLLOW_schema_cident_in_alterTableStatement6339 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00044011EC3A7FFBL});
	public static final BitSet FOLLOW_comparatorType_in_alterTableStatement6344 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000040L});
	public static final BitSet FOLLOW_isStaticColumn_in_alterTableStatement6349 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_190_in_alterTableStatement6371 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_schema_cident_in_alterTableStatement6376 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00044011EC3A7FFBL});
	public static final BitSet FOLLOW_comparatorType_in_alterTableStatement6380 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000040L,0x0000000000000004L});
	public static final BitSet FOLLOW_isStaticColumn_in_alterTableStatement6384 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_194_in_alterTableStatement6407 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_schema_cident_in_alterTableStatement6411 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00044011EC3A7FFBL});
	public static final BitSet FOLLOW_comparatorType_in_alterTableStatement6415 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000040L,0x0000000000000004L});
	public static final BitSet FOLLOW_isStaticColumn_in_alterTableStatement6419 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_191_in_alterTableStatement6426 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_DROP_in_alterTableStatement6440 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x40004011EC3A7FF3L});
	public static final BitSet FOLLOW_schema_cident_in_alterTableStatement6453 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000010000000L});
	public static final BitSet FOLLOW_190_in_alterTableStatement6475 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_schema_cident_in_alterTableStatement6480 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_194_in_alterTableStatement6503 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_schema_cident_in_alterTableStatement6507 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_191_in_alterTableStatement6514 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000010000000L});
	public static final BitSet FOLLOW_K_USING_in_alterTableStatement6536 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000001000L});
	public static final BitSet FOLLOW_K_TIMESTAMP_in_alterTableStatement6538 = new BitSet(new long[]{0x0000000001000000L});
	public static final BitSet FOLLOW_INTEGER_in_alterTableStatement6542 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_RENAME_in_alterTableStatement6558 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_schema_cident_in_alterTableStatement6562 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000008000L});
	public static final BitSet FOLLOW_K_TO_in_alterTableStatement6564 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_schema_cident_in_alterTableStatement6568 = new BitSet(new long[]{0x0000000200000002L});
	public static final BitSet FOLLOW_K_AND_in_alterTableStatement6583 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_schema_cident_in_alterTableStatement6587 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000008000L});
	public static final BitSet FOLLOW_K_TO_in_alterTableStatement6589 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_schema_cident_in_alterTableStatement6593 = new BitSet(new long[]{0x0000000200000002L});
	public static final BitSet FOLLOW_K_WITH_in_alterTableStatement6609 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_properties_in_alterTableStatement6611 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_STATIC_in_isStaticColumn6653 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_ALTER_in_alterMaterializedViewStatement6689 = new BitSet(new long[]{0x0000000000000000L,0x0000001000000000L});
	public static final BitSet FOLLOW_K_MATERIALIZED_in_alterMaterializedViewStatement6691 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000200000000L});
	public static final BitSet FOLLOW_K_VIEW_in_alterMaterializedViewStatement6693 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00006011EC3A7FF3L});
	public static final BitSet FOLLOW_columnFamilyName_in_alterMaterializedViewStatement6697 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000800000000L});
	public static final BitSet FOLLOW_K_WITH_in_alterMaterializedViewStatement6709 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_properties_in_alterMaterializedViewStatement6711 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_ALTER_in_alterTypeStatement6742 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000200000L});
	public static final BitSet FOLLOW_K_TYPE_in_alterTypeStatement6744 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_userTypeName_in_alterTypeStatement6748 = new BitSet(new long[]{0x0000000110000000L,0x1000000000000000L});
	public static final BitSet FOLLOW_K_ALTER_in_alterTypeStatement6768 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_fident_in_alterTypeStatement6774 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000200000L});
	public static final BitSet FOLLOW_K_TYPE_in_alterTypeStatement6776 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00044011EC3A7FFBL});
	public static final BitSet FOLLOW_comparatorType_in_alterTypeStatement6780 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_ADD_in_alterTypeStatement6793 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_fident_in_alterTypeStatement6801 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00044011EC3A7FFBL});
	public static final BitSet FOLLOW_comparatorType_in_alterTypeStatement6805 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_RENAME_in_alterTypeStatement6825 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_fident_in_alterTypeStatement6829 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000008000L});
	public static final BitSet FOLLOW_K_TO_in_alterTypeStatement6831 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_fident_in_alterTypeStatement6835 = new BitSet(new long[]{0x0000000200000002L});
	public static final BitSet FOLLOW_K_AND_in_alterTypeStatement6857 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_fident_in_alterTypeStatement6861 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000008000L});
	public static final BitSet FOLLOW_K_TO_in_alterTypeStatement6863 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_fident_in_alterTypeStatement6867 = new BitSet(new long[]{0x0000000200000002L});
	public static final BitSet FOLLOW_K_DROP_in_dropKeyspaceStatement6919 = new BitSet(new long[]{0x0000000000000000L,0x0000000010000000L});
	public static final BitSet FOLLOW_K_KEYSPACE_in_dropKeyspaceStatement6921 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5CDAF2L,0x00006011EC3A7FF3L});
	public static final BitSet FOLLOW_K_IF_in_dropKeyspaceStatement6924 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000010L});
	public static final BitSet FOLLOW_K_EXISTS_in_dropKeyspaceStatement6926 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00006011EC3A7FF3L});
	public static final BitSet FOLLOW_keyspaceName_in_dropKeyspaceStatement6935 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_DROP_in_dropTableStatement6969 = new BitSet(new long[]{0x0001000000000000L});
	public static final BitSet FOLLOW_K_COLUMNFAMILY_in_dropTableStatement6971 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5CDAF2L,0x00006011EC3A7FF3L});
	public static final BitSet FOLLOW_K_IF_in_dropTableStatement6974 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000010L});
	public static final BitSet FOLLOW_K_EXISTS_in_dropTableStatement6976 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00006011EC3A7FF3L});
	public static final BitSet FOLLOW_columnFamilyName_in_dropTableStatement6985 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_DROP_in_dropTypeStatement7019 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000200000L});
	public static final BitSet FOLLOW_K_TYPE_in_dropTypeStatement7021 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5CDAF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_K_IF_in_dropTypeStatement7024 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000010L});
	public static final BitSet FOLLOW_K_EXISTS_in_dropTypeStatement7026 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_userTypeName_in_dropTypeStatement7035 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_DROP_in_dropIndexStatement7069 = new BitSet(new long[]{0x0000000000000000L,0x0000000000020000L});
	public static final BitSet FOLLOW_K_INDEX_in_dropIndexStatement7071 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5CDAF2L,0x00006011EC3A7FF3L});
	public static final BitSet FOLLOW_K_IF_in_dropIndexStatement7074 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000010L});
	public static final BitSet FOLLOW_K_EXISTS_in_dropIndexStatement7076 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00006011EC3A7FF3L});
	public static final BitSet FOLLOW_indexName_in_dropIndexStatement7085 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_DROP_in_dropMaterializedViewStatement7125 = new BitSet(new long[]{0x0000000000000000L,0x0000001000000000L});
	public static final BitSet FOLLOW_K_MATERIALIZED_in_dropMaterializedViewStatement7127 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000200000000L});
	public static final BitSet FOLLOW_K_VIEW_in_dropMaterializedViewStatement7129 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5CDAF2L,0x00006011EC3A7FF3L});
	public static final BitSet FOLLOW_K_IF_in_dropMaterializedViewStatement7132 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000010L});
	public static final BitSet FOLLOW_K_EXISTS_in_dropMaterializedViewStatement7134 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00006011EC3A7FF3L});
	public static final BitSet FOLLOW_columnFamilyName_in_dropMaterializedViewStatement7143 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_TRUNCATE_in_truncateStatement7174 = new BitSet(new long[]{0xC35FEE2860800000L,0x41F2140EEE5C5AF2L,0x00006011EC3A7FF3L});
	public static final BitSet FOLLOW_K_COLUMNFAMILY_in_truncateStatement7177 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00006011EC3A7FF3L});
	public static final BitSet FOLLOW_columnFamilyName_in_truncateStatement7183 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_GRANT_in_grantPermissionsStatement7208 = new BitSet(new long[]{0x2020004140000000L,0x0000008000000009L,0x0000000000000004L});
	public static final BitSet FOLLOW_permissionOrAll_in_grantPermissionsStatement7220 = new BitSet(new long[]{0x0000000000000000L,0x0001000000000000L});
	public static final BitSet FOLLOW_K_ON_in_grantPermissionsStatement7228 = new BitSet(new long[]{0xC35FEE2860800000L,0x41F2146EFE5C5AF2L,0x00006011EC3A7FF3L});
	public static final BitSet FOLLOW_resource_in_grantPermissionsStatement7240 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000008000L});
	public static final BitSet FOLLOW_K_TO_in_grantPermissionsStatement7248 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00046011EC3A7FF3L});
	public static final BitSet FOLLOW_userOrRoleName_in_grantPermissionsStatement7262 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_REVOKE_in_revokePermissionsStatement7293 = new BitSet(new long[]{0x2020004140000000L,0x0000008000000009L,0x0000000000000004L});
	public static final BitSet FOLLOW_permissionOrAll_in_revokePermissionsStatement7305 = new BitSet(new long[]{0x0000000000000000L,0x0001000000000000L});
	public static final BitSet FOLLOW_K_ON_in_revokePermissionsStatement7313 = new BitSet(new long[]{0xC35FEE2860800000L,0x41F2146EFE5C5AF2L,0x00006011EC3A7FF3L});
	public static final BitSet FOLLOW_resource_in_revokePermissionsStatement7325 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000100L});
	public static final BitSet FOLLOW_K_FROM_in_revokePermissionsStatement7333 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00046011EC3A7FF3L});
	public static final BitSet FOLLOW_userOrRoleName_in_revokePermissionsStatement7347 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_GRANT_in_grantRoleStatement7378 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00046011EC3A7FF3L});
	public static final BitSet FOLLOW_userOrRoleName_in_grantRoleStatement7392 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000008000L});
	public static final BitSet FOLLOW_K_TO_in_grantRoleStatement7400 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00046011EC3A7FF3L});
	public static final BitSet FOLLOW_userOrRoleName_in_grantRoleStatement7414 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_REVOKE_in_revokeRoleStatement7445 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00046011EC3A7FF3L});
	public static final BitSet FOLLOW_userOrRoleName_in_revokeRoleStatement7459 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000100L});
	public static final BitSet FOLLOW_K_FROM_in_revokeRoleStatement7467 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00046011EC3A7FF3L});
	public static final BitSet FOLLOW_userOrRoleName_in_revokeRoleStatement7481 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_LIST_in_listPermissionsStatement7519 = new BitSet(new long[]{0x2020004140000000L,0x0000008000000009L,0x0000000000000004L});
	public static final BitSet FOLLOW_permissionOrAll_in_listPermissionsStatement7531 = new BitSet(new long[]{0x0000000000000002L,0x0001880000000000L});
	public static final BitSet FOLLOW_K_ON_in_listPermissionsStatement7541 = new BitSet(new long[]{0xC35FEE2860800000L,0x41F2146EFE5C5AF2L,0x00006011EC3A7FF3L});
	public static final BitSet FOLLOW_resource_in_listPermissionsStatement7543 = new BitSet(new long[]{0x0000000000000002L,0x0000880000000000L});
	public static final BitSet FOLLOW_K_OF_in_listPermissionsStatement7558 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00046011EC3A7FF3L});
	public static final BitSet FOLLOW_roleName_in_listPermissionsStatement7560 = new BitSet(new long[]{0x0000000000000002L,0x0000080000000000L});
	public static final BitSet FOLLOW_K_NORECURSIVE_in_listPermissionsStatement7574 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_set_in_permission7610 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_ALL_in_permissionOrAll7667 = new BitSet(new long[]{0x0000000000000002L,0x0100000000000000L});
	public static final BitSet FOLLOW_K_PERMISSIONS_in_permissionOrAll7671 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_permission_in_permissionOrAll7692 = new BitSet(new long[]{0x0000000000000002L,0x0080000000000000L});
	public static final BitSet FOLLOW_K_PERMISSION_in_permissionOrAll7696 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_dataResource_in_resource7724 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_roleResource_in_resource7736 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_functionResource_in_resource7748 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_jmxResource_in_resource7760 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_ALL_in_dataResource7783 = new BitSet(new long[]{0x0000000000000000L,0x0000000020000000L});
	public static final BitSet FOLLOW_K_KEYSPACES_in_dataResource7785 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_KEYSPACE_in_dataResource7795 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00006011EC3A7FF3L});
	public static final BitSet FOLLOW_keyspaceName_in_dataResource7801 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_COLUMNFAMILY_in_dataResource7813 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00006011EC3A7FF3L});
	public static final BitSet FOLLOW_columnFamilyName_in_dataResource7822 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_ALL_in_jmxResource7851 = new BitSet(new long[]{0x0000000000000000L,0x0000004000000000L});
	public static final BitSet FOLLOW_K_MBEANS_in_jmxResource7853 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_MBEAN_in_jmxResource7873 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0004000000000000L});
	public static final BitSet FOLLOW_mbean_in_jmxResource7875 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_MBEANS_in_jmxResource7885 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0004000000000000L});
	public static final BitSet FOLLOW_mbean_in_jmxResource7887 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_ALL_in_roleResource7910 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000002L});
	public static final BitSet FOLLOW_K_ROLES_in_roleResource7912 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_ROLE_in_roleResource7922 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00046011EC3A7FF3L});
	public static final BitSet FOLLOW_userOrRoleName_in_roleResource7928 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_ALL_in_functionResource7960 = new BitSet(new long[]{0x0000000000000000L,0x0000000000001000L});
	public static final BitSet FOLLOW_K_FUNCTIONS_in_functionResource7962 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_ALL_in_functionResource7972 = new BitSet(new long[]{0x0000000000000000L,0x0000000000001000L});
	public static final BitSet FOLLOW_K_FUNCTIONS_in_functionResource7974 = new BitSet(new long[]{0x0000000000000000L,0x0000000000010000L});
	public static final BitSet FOLLOW_K_IN_in_functionResource7976 = new BitSet(new long[]{0x0000000000000000L,0x0000000010000000L});
	public static final BitSet FOLLOW_K_KEYSPACE_in_functionResource7978 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00006011EC3A7FF3L});
	public static final BitSet FOLLOW_keyspaceName_in_functionResource7984 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_FUNCTION_in_functionResource7999 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00006011EC3B7FF3L});
	public static final BitSet FOLLOW_functionName_in_functionResource8003 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x4000000000000000L});
	public static final BitSet FOLLOW_190_in_functionResource8021 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x80044011EC3A7FFBL});
	public static final BitSet FOLLOW_comparatorType_in_functionResource8049 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_194_in_functionResource8067 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00044011EC3A7FFBL});
	public static final BitSet FOLLOW_comparatorType_in_functionResource8071 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_191_in_functionResource8099 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_CREATE_in_createUserStatement8147 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000004000000L});
	public static final BitSet FOLLOW_K_USER_in_createUserStatement8149 = new BitSet(new long[]{0x0000000000800000L,0x0000000000008000L,0x0004400000000000L});
	public static final BitSet FOLLOW_K_IF_in_createUserStatement8152 = new BitSet(new long[]{0x0000000000000000L,0x0000200000000000L});
	public static final BitSet FOLLOW_K_NOT_in_createUserStatement8154 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000010L});
	public static final BitSet FOLLOW_K_EXISTS_in_createUserStatement8156 = new BitSet(new long[]{0x0000000000800000L,0x0000000000000000L,0x0004400000000000L});
	public static final BitSet FOLLOW_username_in_createUserStatement8164 = new BitSet(new long[]{0x0000000000000002L,0x0000100000000000L,0x0000000800000200L});
	public static final BitSet FOLLOW_K_WITH_in_createUserStatement8176 = new BitSet(new long[]{0x0000000000000000L,0x0020000000000000L});
	public static final BitSet FOLLOW_userPassword_in_createUserStatement8178 = new BitSet(new long[]{0x0000000000000002L,0x0000100000000000L,0x0000000000000200L});
	public static final BitSet FOLLOW_K_SUPERUSER_in_createUserStatement8192 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_NOSUPERUSER_in_createUserStatement8198 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_ALTER_in_alterUserStatement8243 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000004000000L});
	public static final BitSet FOLLOW_K_USER_in_alterUserStatement8245 = new BitSet(new long[]{0x0000000000800000L,0x0000000000000000L,0x0004400000000000L});
	public static final BitSet FOLLOW_username_in_alterUserStatement8249 = new BitSet(new long[]{0x0000000000000002L,0x0000100000000000L,0x0000000800000200L});
	public static final BitSet FOLLOW_K_WITH_in_alterUserStatement8261 = new BitSet(new long[]{0x0000000000000000L,0x0020000000000000L});
	public static final BitSet FOLLOW_userPassword_in_alterUserStatement8263 = new BitSet(new long[]{0x0000000000000002L,0x0000100000000000L,0x0000000000000200L});
	public static final BitSet FOLLOW_K_SUPERUSER_in_alterUserStatement8277 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_NOSUPERUSER_in_alterUserStatement8291 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_DROP_in_dropUserStatement8337 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000004000000L});
	public static final BitSet FOLLOW_K_USER_in_dropUserStatement8339 = new BitSet(new long[]{0x0000000000800000L,0x0000000000008000L,0x0004400000000000L});
	public static final BitSet FOLLOW_K_IF_in_dropUserStatement8342 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000010L});
	public static final BitSet FOLLOW_K_EXISTS_in_dropUserStatement8344 = new BitSet(new long[]{0x0000000000800000L,0x0000000000000000L,0x0004400000000000L});
	public static final BitSet FOLLOW_username_in_dropUserStatement8352 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_LIST_in_listUsersStatement8377 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000008000000L});
	public static final BitSet FOLLOW_K_USERS_in_listUsersStatement8379 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_CREATE_in_createRoleStatement8413 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000001L});
	public static final BitSet FOLLOW_K_ROLE_in_createRoleStatement8415 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5CDAF2L,0x00046011EC3A7FF3L});
	public static final BitSet FOLLOW_K_IF_in_createRoleStatement8418 = new BitSet(new long[]{0x0000000000000000L,0x0000200000000000L});
	public static final BitSet FOLLOW_K_NOT_in_createRoleStatement8420 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000010L});
	public static final BitSet FOLLOW_K_EXISTS_in_createRoleStatement8422 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00046011EC3A7FF3L});
	public static final BitSet FOLLOW_userOrRoleName_in_createRoleStatement8430 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000800000000L});
	public static final BitSet FOLLOW_K_WITH_in_createRoleStatement8440 = new BitSet(new long[]{0x0000000008000000L,0x0022000400000000L,0x0000000000000200L});
	public static final BitSet FOLLOW_roleOptions_in_createRoleStatement8442 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_ALTER_in_alterRoleStatement8486 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000001L});
	public static final BitSet FOLLOW_K_ROLE_in_alterRoleStatement8488 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00046011EC3A7FF3L});
	public static final BitSet FOLLOW_userOrRoleName_in_alterRoleStatement8492 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000800000000L});
	public static final BitSet FOLLOW_K_WITH_in_alterRoleStatement8502 = new BitSet(new long[]{0x0000000008000000L,0x0022000400000000L,0x0000000000000200L});
	public static final BitSet FOLLOW_roleOptions_in_alterRoleStatement8504 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_DROP_in_dropRoleStatement8548 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000001L});
	public static final BitSet FOLLOW_K_ROLE_in_dropRoleStatement8550 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5CDAF2L,0x00046011EC3A7FF3L});
	public static final BitSet FOLLOW_K_IF_in_dropRoleStatement8553 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000010L});
	public static final BitSet FOLLOW_K_EXISTS_in_dropRoleStatement8555 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00046011EC3A7FF3L});
	public static final BitSet FOLLOW_userOrRoleName_in_dropRoleStatement8563 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_LIST_in_listRolesStatement8603 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000002L});
	public static final BitSet FOLLOW_K_ROLES_in_listRolesStatement8605 = new BitSet(new long[]{0x0000000000000002L,0x0000880000000000L});
	public static final BitSet FOLLOW_K_OF_in_listRolesStatement8615 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00046011EC3A7FF3L});
	public static final BitSet FOLLOW_roleName_in_listRolesStatement8617 = new BitSet(new long[]{0x0000000000000002L,0x0000080000000000L});
	public static final BitSet FOLLOW_K_NORECURSIVE_in_listRolesStatement8630 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_roleOption_in_roleOptions8661 = new BitSet(new long[]{0x0000000200000002L});
	public static final BitSet FOLLOW_K_AND_in_roleOptions8665 = new BitSet(new long[]{0x0000000008000000L,0x0022000400000000L,0x0000000000000200L});
	public static final BitSet FOLLOW_roleOption_in_roleOptions8667 = new BitSet(new long[]{0x0000000200000002L});
	public static final BitSet FOLLOW_K_PASSWORD_in_roleOption8689 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000000800L});
	public static final BitSet FOLLOW_203_in_roleOption8691 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0004000000000000L});
	public static final BitSet FOLLOW_STRING_LITERAL_in_roleOption8695 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_OPTIONS_in_roleOption8706 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000000800L});
	public static final BitSet FOLLOW_203_in_roleOption8708 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000040000L});
	public static final BitSet FOLLOW_fullMapLiteral_in_roleOption8712 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_SUPERUSER_in_roleOption8723 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000000800L});
	public static final BitSet FOLLOW_203_in_roleOption8725 = new BitSet(new long[]{0x0000000000000040L});
	public static final BitSet FOLLOW_BOOLEAN_in_roleOption8729 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_LOGIN_in_roleOption8740 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000000800L});
	public static final BitSet FOLLOW_203_in_roleOption8742 = new BitSet(new long[]{0x0000000000000040L});
	public static final BitSet FOLLOW_BOOLEAN_in_roleOption8746 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_ACCESS_in_roleOption8757 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000008000L});
	public static final BitSet FOLLOW_K_TO_in_roleOption8759 = new BitSet(new long[]{0x0000000040000000L});
	public static final BitSet FOLLOW_K_ALL_in_roleOption8761 = new BitSet(new long[]{0x0080000000000000L});
	public static final BitSet FOLLOW_K_DATACENTERS_in_roleOption8763 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_ACCESS_in_roleOption8774 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000008000L});
	public static final BitSet FOLLOW_K_TO_in_roleOption8776 = new BitSet(new long[]{0x0080000000000000L});
	public static final BitSet FOLLOW_K_DATACENTERS_in_roleOption8778 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000040000L});
	public static final BitSet FOLLOW_210_in_roleOption8780 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0004000000000000L});
	public static final BitSet FOLLOW_dcPermission_in_roleOption8782 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000080004L});
	public static final BitSet FOLLOW_194_in_roleOption8786 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0004000000000000L});
	public static final BitSet FOLLOW_dcPermission_in_roleOption8788 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000080004L});
	public static final BitSet FOLLOW_211_in_roleOption8793 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_STRING_LITERAL_in_dcPermission8813 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_PASSWORD_in_userPassword8835 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0004000000000000L});
	public static final BitSet FOLLOW_STRING_LITERAL_in_userPassword8839 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_EMPTY_QUOTED_NAME_in_cident8871 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_IDENT_in_cident8886 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_QUOTED_NAME_in_cident8911 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_unreserved_keyword_in_cident8930 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_IDENT_in_schema_cident8955 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_QUOTED_NAME_in_schema_cident8980 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_unreserved_keyword_in_schema_cident8999 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_IDENT_in_ident9025 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_QUOTED_NAME_in_ident9050 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_unreserved_keyword_in_ident9069 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_IDENT_in_fident9094 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_QUOTED_NAME_in_fident9119 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_unreserved_keyword_in_fident9138 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_IDENT_in_noncol_ident9164 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_QUOTED_NAME_in_noncol_ident9189 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_unreserved_keyword_in_noncol_ident9208 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ksName_in_keyspaceName9241 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ksName_in_indexName9275 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000000020L});
	public static final BitSet FOLLOW_197_in_indexName9278 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00006011EC3A7FF3L});
	public static final BitSet FOLLOW_idxName_in_indexName9282 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ksName_in_columnFamilyName9314 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000000020L});
	public static final BitSet FOLLOW_197_in_columnFamilyName9317 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00006011EC3A7FF3L});
	public static final BitSet FOLLOW_cfName_in_columnFamilyName9321 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_noncol_ident_in_userTypeName9346 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000000020L});
	public static final BitSet FOLLOW_197_in_userTypeName9348 = new BitSet(new long[]{0x0046A00860800000L,0x41F2140EEC185A70L,0x000040004C3203D3L});
	public static final BitSet FOLLOW_non_type_ident_in_userTypeName9354 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_roleName_in_userOrRoleName9386 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_IDENT_in_ksName9409 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_QUOTED_NAME_in_ksName9434 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_unreserved_keyword_in_ksName9453 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_QMARK_in_ksName9463 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_IDENT_in_cfName9485 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_QUOTED_NAME_in_cfName9510 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_unreserved_keyword_in_cfName9529 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_QMARK_in_cfName9539 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_IDENT_in_idxName9561 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_QUOTED_NAME_in_idxName9586 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_unreserved_keyword_in_idxName9605 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_QMARK_in_idxName9615 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_IDENT_in_roleName9637 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_STRING_LITERAL_in_roleName9662 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_QUOTED_NAME_in_roleName9678 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_unreserved_keyword_in_roleName9697 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_QMARK_in_roleName9707 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_STRING_LITERAL_in_constant9732 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_INTEGER_in_constant9744 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_FLOAT_in_constant9763 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_BOOLEAN_in_constant9784 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_DURATION_in_constant9803 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_UUID_in_constant9821 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_HEXNUMBER_in_constant9843 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_set_in_constant9859 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_POSITIVE_INFINITY_in_constant9879 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_NEGATIVE_INFINITY_in_constant9894 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_210_in_fullMapLiteral9935 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x00000000000C4088L});
	public static final BitSet FOLLOW_term_in_fullMapLiteral9941 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000000080L});
	public static final BitSet FOLLOW_199_in_fullMapLiteral9943 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_term_in_fullMapLiteral9947 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000080004L});
	public static final BitSet FOLLOW_194_in_fullMapLiteral9953 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_term_in_fullMapLiteral9957 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000000080L});
	public static final BitSet FOLLOW_199_in_fullMapLiteral9959 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_term_in_fullMapLiteral9963 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000080004L});
	public static final BitSet FOLLOW_211_in_fullMapLiteral9979 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_mapLiteral_in_setOrMapLiteral10003 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_setLiteral_in_setOrMapLiteral10016 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_194_in_setLiteral10061 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_term_in_setLiteral10065 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_199_in_mapLiteral10110 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_term_in_mapLiteral10114 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_194_in_mapLiteral10120 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_term_in_mapLiteral10124 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000000080L});
	public static final BitSet FOLLOW_199_in_mapLiteral10126 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_term_in_mapLiteral10130 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_listLiteral_in_collectionLiteral10158 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_210_in_collectionLiteral10168 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_term_in_collectionLiteral10172 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000000084L});
	public static final BitSet FOLLOW_setOrMapLiteral_in_collectionLiteral10176 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000080000L});
	public static final BitSet FOLLOW_211_in_collectionLiteral10181 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_210_in_collectionLiteral10199 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000080000L});
	public static final BitSet FOLLOW_211_in_collectionLiteral10201 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_206_in_listLiteral10242 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000054088L});
	public static final BitSet FOLLOW_term_in_listLiteral10248 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000010004L});
	public static final BitSet FOLLOW_194_in_listLiteral10254 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_term_in_listLiteral10258 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000010004L});
	public static final BitSet FOLLOW_208_in_listLiteral10268 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_210_in_usertypeLiteral10312 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_fident_in_usertypeLiteral10316 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000000080L});
	public static final BitSet FOLLOW_199_in_usertypeLiteral10318 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_term_in_usertypeLiteral10322 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000080004L});
	public static final BitSet FOLLOW_194_in_usertypeLiteral10328 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_fident_in_usertypeLiteral10332 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000000080L});
	public static final BitSet FOLLOW_199_in_usertypeLiteral10334 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_term_in_usertypeLiteral10338 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000080004L});
	public static final BitSet FOLLOW_211_in_usertypeLiteral10345 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_190_in_tupleLiteral10382 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_term_in_tupleLiteral10386 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_194_in_tupleLiteral10392 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_term_in_tupleLiteral10396 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_191_in_tupleLiteral10403 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_constant_in_value10426 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_collectionLiteral_in_value10448 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_usertypeLiteral_in_value10461 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_tupleLiteral_in_value10476 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_NULL_in_value10492 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_199_in_value10516 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_noncol_ident_in_value10520 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_QMARK_in_value10531 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_INTEGER_in_intValue10571 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_199_in_intValue10585 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_noncol_ident_in_intValue10589 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_QMARK_in_intValue10600 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_keyspaceName_in_functionName10646 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000000020L});
	public static final BitSet FOLLOW_197_in_functionName10648 = new BitSet(new long[]{0x835EAE2860800000L,0x41F2140EE85C5AF2L,0x00004001EC337FF3L});
	public static final BitSet FOLLOW_allowedFunctionName_in_functionName10654 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_IDENT_in_allowedFunctionName10681 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_QUOTED_NAME_in_allowedFunctionName10715 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_unreserved_function_keyword_in_allowedFunctionName10743 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_TOKEN_in_allowedFunctionName10753 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_COUNT_in_allowedFunctionName10785 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_functionName_in_function10832 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x4000000000000000L});
	public static final BitSet FOLLOW_190_in_function10834 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L});
	public static final BitSet FOLLOW_191_in_function10836 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_functionName_in_function10866 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x4000000000000000L});
	public static final BitSet FOLLOW_190_in_function10868 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_functionArgs_in_function10872 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L});
	public static final BitSet FOLLOW_191_in_function10874 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_term_in_functionArgs10907 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_194_in_functionArgs10913 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_term_in_functionArgs10917 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_termAddition_in_term10945 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_termMultiplication_in_termAddition10997 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000000000000009L});
	public static final BitSet FOLLOW_192_in_termAddition11013 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_termMultiplication_in_termAddition11017 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000000000000009L});
	public static final BitSet FOLLOW_195_in_termAddition11031 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_termMultiplication_in_termAddition11035 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000000000000009L});
	public static final BitSet FOLLOW_termGroup_in_termMultiplication11073 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x2000000000000000L,0x0000000000008040L});
	public static final BitSet FOLLOW_207_in_termMultiplication11089 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_termGroup_in_termMultiplication11093 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x2000000000000000L,0x0000000000008040L});
	public static final BitSet FOLLOW_198_in_termMultiplication11107 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_termGroup_in_termMultiplication11111 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x2000000000000000L,0x0000000000008040L});
	public static final BitSet FOLLOW_189_in_termMultiplication11125 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_termGroup_in_termMultiplication11129 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x2000000000000000L,0x0000000000008040L});
	public static final BitSet FOLLOW_simpleTerm_in_termGroup11165 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_195_in_termGroup11188 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044080L});
	public static final BitSet FOLLOW_simpleTerm_in_termGroup11193 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_value_in_simpleTerm11226 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_function_in_simpleTerm11270 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_190_in_simpleTerm11309 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00044011EC3A7FFBL});
	public static final BitSet FOLLOW_comparatorType_in_simpleTerm11313 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L});
	public static final BitSet FOLLOW_191_in_simpleTerm11315 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044080L});
	public static final BitSet FOLLOW_simpleTerm_in_simpleTerm11319 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_cident_in_columnOperation11343 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000004832L});
	public static final BitSet FOLLOW_columnOperationDifferentiator_in_columnOperation11345 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_203_in_columnOperationDifferentiator11364 = new BitSet(new long[]{0xC35EEE2861A24840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_normalColumnOperation_in_columnOperationDifferentiator11366 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_shorthandColumnOperation_in_columnOperationDifferentiator11375 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_206_in_columnOperationDifferentiator11384 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_term_in_columnOperationDifferentiator11388 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000010000L});
	public static final BitSet FOLLOW_208_in_columnOperationDifferentiator11390 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000000800L});
	public static final BitSet FOLLOW_collectionColumnOperation_in_columnOperationDifferentiator11392 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_197_in_columnOperationDifferentiator11401 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_fident_in_columnOperationDifferentiator11405 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000000800L});
	public static final BitSet FOLLOW_udtColumnOperation_in_columnOperationDifferentiator11407 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_term_in_normalColumnOperation11428 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000000000000001L});
	public static final BitSet FOLLOW_192_in_normalColumnOperation11431 = new BitSet(new long[]{0xC35EEE2860804000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_cident_in_normalColumnOperation11435 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_cident_in_normalColumnOperation11456 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000000009L});
	public static final BitSet FOLLOW_set_in_normalColumnOperation11460 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_term_in_normalColumnOperation11470 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_cident_in_normalColumnOperation11488 = new BitSet(new long[]{0x0000000001000000L});
	public static final BitSet FOLLOW_INTEGER_in_normalColumnOperation11492 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_set_in_shorthandColumnOperation11520 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_term_in_shorthandColumnOperation11530 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_203_in_collectionColumnOperation11556 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_term_in_collectionColumnOperation11560 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_203_in_udtColumnOperation11586 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_term_in_udtColumnOperation11590 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_cident_in_columnCondition11623 = new BitSet(new long[]{0x0000000000000000L,0x0000000000010000L,0x1000000000000000L,0x0000000000007E20L});
	public static final BitSet FOLLOW_relationType_in_columnCondition11637 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_term_in_columnCondition11641 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_IN_in_columnCondition11655 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x4000200000000000L,0x0000000000000080L});
	public static final BitSet FOLLOW_singleColumnInValues_in_columnCondition11673 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_inMarker_in_columnCondition11693 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_206_in_columnCondition11721 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_term_in_columnCondition11725 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000010000L});
	public static final BitSet FOLLOW_208_in_columnCondition11727 = new BitSet(new long[]{0x0000000000000000L,0x0000000000010000L,0x1000000000000000L,0x0000000000003E00L});
	public static final BitSet FOLLOW_relationType_in_columnCondition11745 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_term_in_columnCondition11749 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_IN_in_columnCondition11767 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x4000200000000000L,0x0000000000000080L});
	public static final BitSet FOLLOW_singleColumnInValues_in_columnCondition11789 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_inMarker_in_columnCondition11813 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_197_in_columnCondition11859 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_fident_in_columnCondition11863 = new BitSet(new long[]{0x0000000000000000L,0x0000000000010000L,0x1000000000000000L,0x0000000000003E00L});
	public static final BitSet FOLLOW_relationType_in_columnCondition11881 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_term_in_columnCondition11885 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_IN_in_columnCondition11903 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x4000200000000000L,0x0000000000000080L});
	public static final BitSet FOLLOW_singleColumnInValues_in_columnCondition11925 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_inMarker_in_columnCondition11949 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_property_in_properties12011 = new BitSet(new long[]{0x0000000200000002L});
	public static final BitSet FOLLOW_K_AND_in_properties12015 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_property_in_properties12017 = new BitSet(new long[]{0x0000000200000002L});
	public static final BitSet FOLLOW_noncol_ident_in_property12040 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000000800L});
	public static final BitSet FOLLOW_203_in_property12042 = new BitSet(new long[]{0xC35EEE2861220840L,0x47F2170EEE5C5AF2L,0x00240011EC3A7FF3L});
	public static final BitSet FOLLOW_propertyValue_in_property12046 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_noncol_ident_in_property12058 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000000800L});
	public static final BitSet FOLLOW_203_in_property12060 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000040000L});
	public static final BitSet FOLLOW_fullMapLiteral_in_property12064 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_constant_in_propertyValue12089 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_unreserved_keyword_in_propertyValue12111 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_203_in_relationType12134 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_201_in_relationType12145 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_202_in_relationType12156 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_204_in_relationType12166 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_205_in_relationType12177 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_188_in_relationType12187 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_cident_in_relation12209 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x1000000000000000L,0x0000000000003E00L});
	public static final BitSet FOLLOW_relationType_in_relation12213 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_term_in_relation12217 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_cident_in_relation12229 = new BitSet(new long[]{0x0000000000000000L,0x0000000080000000L});
	public static final BitSet FOLLOW_K_LIKE_in_relation12231 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_term_in_relation12235 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_cident_in_relation12247 = new BitSet(new long[]{0x0000000000000000L,0x0000000001000000L});
	public static final BitSet FOLLOW_K_IS_in_relation12249 = new BitSet(new long[]{0x0000000000000000L,0x0000200000000000L});
	public static final BitSet FOLLOW_K_NOT_in_relation12251 = new BitSet(new long[]{0x0000000000000000L,0x0000400000000000L});
	public static final BitSet FOLLOW_K_NULL_in_relation12253 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_TOKEN_in_relation12263 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x4000000000000000L});
	public static final BitSet FOLLOW_tupleOfIdentifiers_in_relation12267 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x1000000000000000L,0x0000000000003E00L});
	public static final BitSet FOLLOW_relationType_in_relation12271 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_term_in_relation12275 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_cident_in_relation12295 = new BitSet(new long[]{0x0000000000000000L,0x0000000000010000L});
	public static final BitSet FOLLOW_K_IN_in_relation12297 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000200000000000L,0x0000000000000080L});
	public static final BitSet FOLLOW_inMarker_in_relation12301 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_cident_in_relation12321 = new BitSet(new long[]{0x0000000000000000L,0x0000000000010000L});
	public static final BitSet FOLLOW_K_IN_in_relation12323 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x4000000000000000L});
	public static final BitSet FOLLOW_singleColumnInValues_in_relation12327 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_cident_in_relation12347 = new BitSet(new long[]{0x0004000000000000L});
	public static final BitSet FOLLOW_containsOperator_in_relation12351 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_term_in_relation12355 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_cident_in_relation12367 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000004000L});
	public static final BitSet FOLLOW_206_in_relation12369 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_term_in_relation12373 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000010000L});
	public static final BitSet FOLLOW_208_in_relation12375 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x1000000000000000L,0x0000000000003E00L});
	public static final BitSet FOLLOW_relationType_in_relation12379 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_term_in_relation12383 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_tupleOfIdentifiers_in_relation12395 = new BitSet(new long[]{0x0000000000000000L,0x0000000000010000L,0x1000000000000000L,0x0000000000003E00L});
	public static final BitSet FOLLOW_K_IN_in_relation12405 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x4000200000000000L,0x0000000000000080L});
	public static final BitSet FOLLOW_190_in_relation12419 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L});
	public static final BitSet FOLLOW_191_in_relation12421 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_inMarkerForTuple_in_relation12453 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_tupleOfTupleLiterals_in_relation12487 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_tupleOfMarkersForTuples_in_relation12521 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_relationType_in_relation12563 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x4000000000000000L});
	public static final BitSet FOLLOW_tupleLiteral_in_relation12567 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_relationType_in_relation12593 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000200000000000L,0x0000000000000080L});
	public static final BitSet FOLLOW_markerForTuple_in_relation12597 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_190_in_relation12627 = new BitSet(new long[]{0xC35EEE2860804000L,0x41F2140EEE5C5AF2L,0x40004011EC3B7FF3L});
	public static final BitSet FOLLOW_relation_in_relation12629 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L});
	public static final BitSet FOLLOW_191_in_relation12632 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_CONTAINS_in_containsOperator12653 = new BitSet(new long[]{0x0000000000000002L,0x0000000004000000L});
	public static final BitSet FOLLOW_K_KEY_in_containsOperator12658 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_QMARK_in_inMarker12683 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_199_in_inMarker12693 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_noncol_ident_in_inMarker12697 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_190_in_tupleOfIdentifiers12729 = new BitSet(new long[]{0xC35EEE2860804000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_cident_in_tupleOfIdentifiers12733 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_194_in_tupleOfIdentifiers12738 = new BitSet(new long[]{0xC35EEE2860804000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_cident_in_tupleOfIdentifiers12742 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_191_in_tupleOfIdentifiers12748 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_190_in_singleColumnInValues12778 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0xC0246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_term_in_singleColumnInValues12786 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_194_in_singleColumnInValues12791 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x0000000000044088L});
	public static final BitSet FOLLOW_term_in_singleColumnInValues12795 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_191_in_singleColumnInValues12804 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_190_in_tupleOfTupleLiterals12834 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x4000000000000000L});
	public static final BitSet FOLLOW_tupleLiteral_in_tupleOfTupleLiterals12838 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_194_in_tupleOfTupleLiterals12843 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x4000000000000000L});
	public static final BitSet FOLLOW_tupleLiteral_in_tupleOfTupleLiterals12847 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_191_in_tupleOfTupleLiterals12853 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_QMARK_in_markerForTuple12874 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_199_in_markerForTuple12884 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_noncol_ident_in_markerForTuple12888 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_190_in_tupleOfMarkersForTuples12920 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000200000000000L,0x0000000000000080L});
	public static final BitSet FOLLOW_markerForTuple_in_tupleOfMarkersForTuples12924 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_194_in_tupleOfMarkersForTuples12929 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000200000000000L,0x0000000000000080L});
	public static final BitSet FOLLOW_markerForTuple_in_tupleOfMarkersForTuples12933 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_191_in_tupleOfMarkersForTuples12939 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_QMARK_in_inMarkerForTuple12960 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_199_in_inMarkerForTuple12970 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00004011EC3A7FF3L});
	public static final BitSet FOLLOW_noncol_ident_in_inMarkerForTuple12974 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_native_type_in_comparatorType12999 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_collection_type_in_comparatorType13015 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_tuple_type_in_comparatorType13027 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_userTypeName_in_comparatorType13043 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_FROZEN_in_comparatorType13055 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000000200L});
	public static final BitSet FOLLOW_201_in_comparatorType13057 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00044011EC3A7FFBL});
	public static final BitSet FOLLOW_comparatorType_in_comparatorType13061 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000001000L});
	public static final BitSet FOLLOW_204_in_comparatorType13063 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_STRING_LITERAL_in_comparatorType13081 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_ASCII_in_native_type13110 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_BIGINT_in_native_type13124 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_BLOB_in_native_type13137 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_BOOLEAN_in_native_type13152 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_COUNTER_in_native_type13164 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_DECIMAL_in_native_type13176 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_DOUBLE_in_native_type13188 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_DURATION_in_native_type13201 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_FLOAT_in_native_type13214 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_INET_in_native_type13228 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_INT_in_native_type13243 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_SMALLINT_in_native_type13259 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_TEXT_in_native_type13270 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_TIMESTAMP_in_native_type13285 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_TINYINT_in_native_type13295 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_UUID_in_native_type13307 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_VARCHAR_in_native_type13322 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_VARINT_in_native_type13334 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_TIMEUUID_in_native_type13347 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_DATE_in_native_type13358 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_TIME_in_native_type13373 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_MAP_in_collection_type13401 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000000200L});
	public static final BitSet FOLLOW_201_in_collection_type13404 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00044011EC3A7FFBL});
	public static final BitSet FOLLOW_comparatorType_in_collection_type13408 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_194_in_collection_type13410 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00044011EC3A7FFBL});
	public static final BitSet FOLLOW_comparatorType_in_collection_type13414 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000001000L});
	public static final BitSet FOLLOW_204_in_collection_type13416 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_LIST_in_collection_type13434 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000000200L});
	public static final BitSet FOLLOW_201_in_collection_type13436 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00044011EC3A7FFBL});
	public static final BitSet FOLLOW_comparatorType_in_collection_type13440 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000001000L});
	public static final BitSet FOLLOW_204_in_collection_type13442 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_SET_in_collection_type13460 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000000200L});
	public static final BitSet FOLLOW_201_in_collection_type13463 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00044011EC3A7FFBL});
	public static final BitSet FOLLOW_comparatorType_in_collection_type13467 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000001000L});
	public static final BitSet FOLLOW_204_in_collection_type13469 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_TUPLE_in_tuple_type13518 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000000200L});
	public static final BitSet FOLLOW_201_in_tuple_type13520 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00044011EC3A7FFBL});
	public static final BitSet FOLLOW_comparatorType_in_tuple_type13524 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000001004L});
	public static final BitSet FOLLOW_194_in_tuple_type13529 = new BitSet(new long[]{0xC35EEE2860800000L,0x41F2140EEE5C5AF2L,0x00044011EC3A7FFBL});
	public static final BitSet FOLLOW_comparatorType_in_tuple_type13533 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000001004L});
	public static final BitSet FOLLOW_204_in_tuple_type13539 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_IDENT_in_username13556 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_STRING_LITERAL_in_username13564 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_QUOTED_NAME_in_username13572 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_STRING_LITERAL_in_mbean13591 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_IDENT_in_non_type_ident13616 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_QUOTED_NAME_in_non_type_ident13647 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_basic_unreserved_keyword_in_non_type_ident13672 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_KEY_in_non_type_ident13684 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_unreserved_function_keyword_in_unreserved_keyword13727 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_set_in_unreserved_keyword13743 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_basic_unreserved_keyword_in_unreserved_function_keyword13794 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_native_type_in_unreserved_function_keyword13806 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_set_in_basic_unreserved_keyword13844 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_JSON_in_synpred1_Parser1062 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x000000000004C088L});
	public static final BitSet FOLLOW_selectClause_in_synpred1_Parser1064 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_K_DISTINCT_in_synpred2_Parser1265 = new BitSet(new long[]{0xC35EEE2861A20840L,0x47F2570EEE5C5AF2L,0x40246011EC3B7FF3L,0x000000000004C088L});
	public static final BitSet FOLLOW_selectors_in_synpred2_Parser1267 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_selectionGroupWithField_in_synpred3_Parser1596 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_selectionTypeHint_in_synpred4_Parser1883 = new BitSet(new long[]{0x0000000000000002L});
}
