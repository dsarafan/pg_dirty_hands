CREATE OR REPLACE FUNCTION freeze_tuple(regclass, tid, force bool DEFAULT false)
RETURNS boolean AS 'MODULE_PATHNAME' LANGUAGE C;
CREATE OR REPLACE FUNCTION freeze_tuple_unlogged(regclass, tid)
RETURNS boolean AS 'MODULE_PATHNAME' LANGUAGE C;
