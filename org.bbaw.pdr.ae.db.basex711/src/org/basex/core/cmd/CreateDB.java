package org.basex.core.cmd;

import static org.basex.core.Text.DB_PINNED_X;
import static org.basex.core.Text.FILE_NOT_FOUND_X;
import static org.basex.core.Text.PERM_NEEDED_X;

import java.io.BufferedInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;

import javax.xml.transform.sax.SAXSource;

import org.basex.build.Builder;
import org.basex.build.DirParser;
import org.basex.build.DiskBuilder;
import org.basex.build.MemBuilder;
import org.basex.build.Parser;
import org.basex.build.xml.SAXWrapper;
import org.basex.core.BaseXException;
import org.basex.core.CommandBuilder;
import org.basex.core.Commands.Cmd;
import org.basex.core.Commands.CmdCreate;
import org.basex.core.Commands.CmdPerm;
import org.basex.core.Context;
import org.basex.core.Prop;
import org.basex.core.User;
import org.basex.data.Data;
import org.basex.data.MemData;
import org.basex.index.IndexToken.IndexType;
import org.basex.index.ft.FTBuilder;
import org.basex.index.value.ValueBuilder;
import org.basex.io.IO;
import org.basex.io.IOContent;
import org.basex.io.in.BufferInput;
import org.basex.io.in.LookupInput;
import org.basex.util.Util;
import org.xml.sax.InputSource;

/**
 * Evaluates the 'create db' command and creates a new database.
 *
 * @author BaseX Team 2005-12, BSD License
 * @author Christian Gruen
 */
public final class CreateDB extends ACreate {
  /**
   * Default constructor.
   * @param name name of database
   */
  public CreateDB(final String name) {
    this(name, null);
  }

  /**
   * Constructor, specifying an initial database input.
   * @param name name of database
   * @param input input reference (local/remote file or XML string)
   */
  public CreateDB(final String name, final String input) {
    super(name, input);
  }

  @Override
  protected boolean run() {
    final String name = args[0];
    IO io = null;

    Parser parser = Parser.emptyParser();
    final String format = prop.get(Prop.PARSER);
    if(args.length < 1 || args[1] == null) {
      if(in != null && in.getByteStream() != null) {
        try {
          io = cache();
          if(io == null) {
            InputStream is = in.getByteStream();
            if(!(is instanceof BufferedInputStream ||
                is instanceof BufferInput)) is = new BufferedInputStream(is);

            final LookupInput li = new LookupInput(is);
            if(li.lookup() != -1) {
              parser = new SAXWrapper(new SAXSource(new InputSource(li)),
                  name + '.' + format, "", context.prop);
            }
          }
        } catch(final IOException ex) {
          Util.debug(ex);
          return error(Util.message(ex));
        }
      }
    } else {
      io = IO.get(args[1]);
    }

    if(io != null) {
      if(!io.exists()) return error(FILE_NOT_FOUND_X, io);
      if(io instanceof IOContent) io.name(name + '.' + format);
      parser = new DirParser(io, prop, mprop.dbpath(name));
    }

    return build(parser, name);
  }

  /**
   * Returns a database instance from the specified parser.
   * @param name name of the database
   * @param parser input parser
   * @param ctx database context
   * @return new database instance
   * @throws IOException I/O exception
   */
  public static synchronized Data create(final String name, final Parser parser,
      final Context ctx) throws IOException {

    // check permissions
    if(!ctx.user.perm(User.CREATE))
      throw new BaseXException(PERM_NEEDED_X, CmdPerm.CREATE);

    // create main memory database instance
    final Prop prop = ctx.prop;
    if(prop.is(Prop.MAINMEM)) return MemBuilder.build(name, parser, ctx.prop);

    // database is currently locked by another process
    if(ctx.pinned(name)) throw new BaseXException(DB_PINNED_X, name);

    // create disk builder, set database path
    final Builder builder = new DiskBuilder(name, parser, ctx);

    // build database and index structures
    try {
      final Data data = builder.build();
      if(data.meta.createtext) data.setIndex(IndexType.TEXT,
        new ValueBuilder(data, true).build());
      if(data.meta.createattr) data.setIndex(IndexType.ATTRIBUTE,
        new ValueBuilder(data, false).build());
      if(data.meta.createftxt) data.setIndex(IndexType.FULLTEXT,
        FTBuilder.get(data).build());
      data.meta.pathindex = data.meta.createpath;
      data.close();
    } finally {
      try { builder.close(); } catch(final IOException exx) { Util.debug(exx); }
    }
    return Open.open(name, ctx);
  }

  /**
   * Returns a main memory database instance from the specified parser.
   * @param parser input parser
   * @param ctx database context
   * @return new database instance
   * @throws IOException I/O exception
   */
  public static synchronized MemData mainMem(final Parser parser,
      final Context ctx) throws IOException {

    if(ctx.user.perm(User.CREATE)) return MemBuilder.build(parser, ctx.prop);
    throw new BaseXException(PERM_NEEDED_X, CmdPerm.CREATE);
  }

  /**
   * Returns a main memory database instance for the specified input reference.
   * @param source document source
   * @param ctx database context
   * @return new database instance
   * @throws IOException I/O exception
   */
  public static synchronized MemData mainMem(final IO source, final Context ctx)
      throws IOException {

    if(!source.exists()) throw new FileNotFoundException(
        Util.info(FILE_NOT_FOUND_X, source));
    return mainMem(new DirParser(source, ctx.prop, null), ctx);
  }

  @Override
  public void build(final CommandBuilder cb) {
    cb.init(Cmd.CREATE + " " + CmdCreate.DB).args();
  }
}
