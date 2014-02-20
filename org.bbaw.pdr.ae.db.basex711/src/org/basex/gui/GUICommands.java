package org.basex.gui;

import static org.basex.core.Text.ABOUT;
import static org.basex.core.Text.BUTTONS;
import static org.basex.core.Text.CHECK_FOR_UPDATES;
import static org.basex.core.Text.CLOSE;
import static org.basex.core.Text.COLORS;
import static org.basex.core.Text.COMMUNITY;
import static org.basex.core.Text.COMMUNITY_URL;
import static org.basex.core.Text.COPY;
import static org.basex.core.Text.COPY_PATH;
import static org.basex.core.Text.CREATING_DB;
import static org.basex.core.Text.DELETE;
import static org.basex.core.Text.DELETE_NODES;
import static org.basex.core.Text.DOC_URL;
import static org.basex.core.Text.DOTS;
import static org.basex.core.Text.EDIT;
import static org.basex.core.Text.EDITOR;
import static org.basex.core.Text.EXIT;
import static org.basex.core.Text.EXPLORER;
import static org.basex.core.Text.EXPORT_XML;
import static org.basex.core.Text.FILES_REPLACE_X;
import static org.basex.core.Text.FILE_EXISTS_X;
import static org.basex.core.Text.FILTER_SELECTED;
import static org.basex.core.Text.FOLDER;
import static org.basex.core.Text.FONTS_D;
import static org.basex.core.Text.FULLSCREEN;
import static org.basex.core.Text.GO_BACK;
import static org.basex.core.Text.GO_FORWARD;
import static org.basex.core.Text.GO_HOME;
import static org.basex.core.Text.GO_UP;
import static org.basex.core.Text.HELP;
import static org.basex.core.Text.H_ABOUT;
import static org.basex.core.Text.H_BUTTONS;
import static org.basex.core.Text.H_CLOSE;
import static org.basex.core.Text.H_CLOSE_FILE;
import static org.basex.core.Text.H_COLORS;
import static org.basex.core.Text.H_COMMUNITY;
import static org.basex.core.Text.H_COPY;
import static org.basex.core.Text.H_CPPATH;
import static org.basex.core.Text.H_DELETE;
import static org.basex.core.Text.H_EDIT;
import static org.basex.core.Text.H_EDITOR;
import static org.basex.core.Text.H_EXIT;
import static org.basex.core.Text.H_EXPLORER;
import static org.basex.core.Text.H_EXPORT_XML;
import static org.basex.core.Text.H_FILTER_SELECTED;
import static org.basex.core.Text.H_FOLDER;
import static org.basex.core.Text.H_FONTS;
import static org.basex.core.Text.H_FULLSCREEN;
import static org.basex.core.Text.H_GO_HOME;
import static org.basex.core.Text.H_GO_UP;
import static org.basex.core.Text.H_HELP;
import static org.basex.core.Text.H_INPUT_BAR;
import static org.basex.core.Text.H_MAP;
import static org.basex.core.Text.H_MAP_LAYOUT;
import static org.basex.core.Text.H_NEW;
import static org.basex.core.Text.H_NEW_FILE;
import static org.basex.core.Text.H_NEW_NODE;
import static org.basex.core.Text.H_OPEN_FILE;
import static org.basex.core.Text.H_OPEN_MANAGE;
import static org.basex.core.Text.H_PASTE;
import static org.basex.core.Text.H_PLOT;
import static org.basex.core.Text.H_PREFERENCES;
import static org.basex.core.Text.H_PROPERTIES;
import static org.basex.core.Text.H_QUERY_INFO;
import static org.basex.core.Text.H_RT_EXECUTION;
import static org.basex.core.Text.H_RT_FILTERING;
import static org.basex.core.Text.H_SAVE;
import static org.basex.core.Text.H_STATUS_BAR;
import static org.basex.core.Text.H_TABLE;
import static org.basex.core.Text.H_TEXT;
import static org.basex.core.Text.H_TREE;
import static org.basex.core.Text.H_TREE_OPTIONS;
import static org.basex.core.Text.H_UPDATES;
import static org.basex.core.Text.INPUT_BAR;
import static org.basex.core.Text.MAP;
import static org.basex.core.Text.MAP_LAYOUT_D;
import static org.basex.core.Text.NEW;
import static org.basex.core.Text.NEW_DB_QUESTION;
import static org.basex.core.Text.OPEN;
import static org.basex.core.Text.OPEN_MANAGE;
import static org.basex.core.Text.PASTE;
import static org.basex.core.Text.PLOT;
import static org.basex.core.Text.PREFERENCES;
import static org.basex.core.Text.PROPERTIES;
import static org.basex.core.Text.QUERY_INFO;
import static org.basex.core.Text.RT_EXECUCTION;
import static org.basex.core.Text.RT_FILTERING;
import static org.basex.core.Text.SAVE;
import static org.basex.core.Text.SAVE_AS;
import static org.basex.core.Text.STATUS_BAR;
import static org.basex.core.Text.S_H_SERVER_ADMIN;
import static org.basex.core.Text.S_SERVER_ADMIN;
import static org.basex.core.Text.TABLE;
import static org.basex.core.Text.TEXT;
import static org.basex.core.Text.TREE;
import static org.basex.core.Text.TREE_OPTIONS_D;
import static org.basex.core.Text.UPDATE_URL;

import java.awt.BorderLayout;
import java.awt.Toolkit;
import java.awt.datatransfer.Clipboard;
import java.awt.datatransfer.StringSelection;

import javax.swing.AbstractButton;

import org.basex.core.Context;
import org.basex.core.Prop;
import org.basex.core.cmd.Close;
import org.basex.core.cmd.CreateDB;
import org.basex.core.cmd.Cs;
import org.basex.core.cmd.Export;
import org.basex.core.cmd.XQuery;
import org.basex.data.Data;
import org.basex.data.Nodes;
import org.basex.gui.dialog.Dialog;
import org.basex.gui.dialog.DialogAbout;
import org.basex.gui.dialog.DialogColors;
import org.basex.gui.dialog.DialogEdit;
import org.basex.gui.dialog.DialogExport;
import org.basex.gui.dialog.DialogFonts;
import org.basex.gui.dialog.DialogInsert;
import org.basex.gui.dialog.DialogManage;
import org.basex.gui.dialog.DialogMapLayout;
import org.basex.gui.dialog.DialogNew;
import org.basex.gui.dialog.DialogPrefs;
import org.basex.gui.dialog.DialogProgress;
import org.basex.gui.dialog.DialogProps;
import org.basex.gui.dialog.DialogServer;
import org.basex.gui.dialog.DialogTreeOptions;
import org.basex.gui.view.ViewData;
import org.basex.io.IO;
import org.basex.io.IOFile;
import org.basex.query.func.Function;
import org.basex.query.item.ANode;
import org.basex.query.item.Int;
import org.basex.query.item.NodeType;
import org.basex.query.item.Str;
import org.basex.util.Token;
import org.basex.util.Util;
import org.basex.util.list.IntList;
import org.basex.util.list.StringList;

/**
 * This enumeration encapsulates all commands that are triggered by
 * GUI operations.
 *
 * @author BaseX Team 2005-12, BSD License
 * @author Christian Gruen
 */
public enum GUICommands implements GUICommand {

  /* DATABASE MENU */

  /** Opens a dialog to create a new database. */
  C_CREATE(NEW + DOTS, "% N", H_NEW, false, false) {
    @Override
    public void execute(final GUI gui) {
      // open file chooser for XML creation
      final DialogNew dialog = new DialogNew(gui);
      if(!dialog.ok()) return;
      final String in = gui.gprop.get(GUIProp.CREATEPATH);
      final String db = gui.gprop.get(GUIProp.CREATENAME);
      DialogProgress.execute(dialog, CREATING_DB,
          new CreateDB(db, in.isEmpty() ? null : in));
    }
  },

  /** Opens a dialog to manage databases. */
  C_OPEN_MANAGE(OPEN_MANAGE + DOTS, "% O", H_OPEN_MANAGE, false, false) {
    @Override
    public void execute(final GUI gui) {
      if(new DialogManage(gui, true).nodb()) {
        if(Dialog.confirm(gui, NEW_DB_QUESTION)) C_CREATE.execute(gui);
      }
    }
  },

  /** Shows database info. */
  C_INFO(PROPERTIES + DOTS, "% D", H_PROPERTIES, true, false) {
    @Override
    public void execute(final GUI gui) {
      new DialogProps(gui);
    }
  },

  /** Exports a database. */
  C_EXPORT(EXPORT_XML + DOTS, null, H_EXPORT_XML, true, false) {
    @Override
    public void execute(final GUI gui) {
      final DialogExport dialog = new DialogExport(gui);
      if(!dialog.ok()) return;

      final IOFile root = new IOFile(dialog.path());

      // check if existing files will be overwritten
      if(root.exists()) {
        IO file = null;
        boolean overwrite = false;
        final Data d = gui.context.data();
        final IntList il = d.resources.docs();
        for(int i = 0, is = il.size(); i < is; i++) {
          file = root.merge(Token.string(d.text(il.get(i), true)));
          if(file.exists()) {
            if(overwrite) {
              // more than one file will be overwritten; check remaining tests
              file = null;
              break;
            }
            overwrite = true;
          }
        }
        if(overwrite) {
          // show message for overwriting files or directories
          final String msg = file == null ? FILES_REPLACE_X : FILE_EXISTS_X;
          if(file == null) file = root;
          if(!Dialog.confirm(gui, Util.info(msg, file))) return;
        }
      }
      gui.execute(new Export(root.path()));
    }

    @Override
    public void refresh(final GUI gui, final AbstractButton b) {
      b.setEnabled(gui.context.data() != null && !gui.context.data().empty());
    }
  },

  /** Closes the database. */
  C_CLOSE(CLOSE, "% W", H_CLOSE, true, false) {
    @Override
    public void execute(final GUI gui) {
      gui.execute(new Close());
    }
  },

  /** Server Dialog. */
  C_SERVER(S_SERVER_ADMIN + DOTS, null, S_H_SERVER_ADMIN, false, false) {
    @Override
    public void execute(final GUI gui) {
      // open file chooser for XML creation
      new DialogServer(gui);
    }
  },

  /** Opens a query file. */
  C_EDITNEW(NEW + DOTS, "% shift N", H_NEW_FILE, false, false) {
    @Override
    public void execute(final GUI gui) {
      gui.editor.newFile();
    }
  },

  /** Opens a new editor file. */
  C_EDITOPEN(OPEN + DOTS, "% R", H_OPEN_FILE, false, false) {
    @Override
    public void execute(final GUI gui) {
      gui.editor.open();
    }
  },

  /** Saves the current editor file. */
  C_EDITSAVE(SAVE, "% S", H_SAVE, false, false) {
    @Override
    public void execute(final GUI gui) {
      gui.editor.save();
    }

    @Override
    public void refresh(final GUI gui, final AbstractButton b) {
      b.setEnabled(gui.editor != null && gui.editor.saveable());
    }
  },

  /** Saves the current editor file under a new name. */
  C_EDITSAVEAS(SAVE_AS + DOTS, "% shift S", H_SAVE, false, false) {
    @Override
    public void execute(final GUI gui) {
      gui.editor.saveAs();
    }
  },

  /** Closes the current editor file. */
  C_EDITCLOSE(CLOSE, "% shift W", H_CLOSE_FILE, false, false) {
    @Override
    public void execute(final GUI gui) {
      gui.editor.close(null);
    }
  },

  /** Exits the application. */
  C_EXIT(EXIT, "% Q", H_EXIT, false, false) {
    @Override
    public void execute(final GUI gui) {
      gui.dispose();
    }
  },

  /* EDIT COMMANDS */

  /** Copies the current path. */
  C_COPYPATH(COPY_PATH, "% shift C", H_CPPATH, true, false) {
    @Override
    public void execute(final GUI gui) {
      final int pre = gui.context.marked.list[0];
      final byte[] txt = ViewData.path(gui.context.data(), pre);
      // copy path to clipboard
      final Clipboard clip = Toolkit.getDefaultToolkit().getSystemClipboard();
      clip.setContents(new StringSelection(Token.string(txt)), null);
    }

    @Override
    public void refresh(final GUI gui, final AbstractButton b) {
      // disallow copy of empty node set or root node
      final Nodes marked = gui.context.marked;
      b.setEnabled(marked != null && marked.size() != 0);
    }
  },

  /** Copies the currently marked nodes. */
  C_COPY(COPY, "", H_COPY, true, false) {
    @Override
    public void execute(final GUI gui) {
      final Context ctx = gui.context;
      final Nodes n = ctx.marked;
      ctx.copied = new Nodes(n.list, n.data);
    }

    @Override
    public void refresh(final GUI gui, final AbstractButton b) {
      // disallow copy of empty node set or root node
      b.setEnabled(updatable(gui.context.marked));
    }
  },

  /** Pastes the copied nodes. */
  C_PASTE(PASTE, "", H_PASTE, true, false) {
    @Override
    public void execute(final GUI gui) {
      final StringBuilder sb = new StringBuilder();
      final Nodes n = gui.context.copied;
      for(int i = 0; i < n.size(); ++i) {
        if(i > 0) sb.append(',');
        sb.append(openPre(n, i));
      }
      gui.context.copied = null;
      gui.execute(new XQuery("insert nodes (" + sb + ") into " +
        openPre(gui.context.marked, 0)));
    }

    @Override
    public void refresh(final GUI gui, final AbstractButton b) {
      final Context ctx = gui.context;
      // disallow copy of empty node set or root node
      b.setEnabled(updatable(ctx.marked, Data.DOC) && ctx.copied != null);
    }
  },

  /** Deletes the currently marked nodes. */
  C_DELETE(DELETE + DOTS, "", H_DELETE, true, false) {
    @Override
    public void execute(final GUI gui) {
      if(!Dialog.confirm(gui, DELETE_NODES)) return;
      final StringBuilder sb = new StringBuilder();
      final Nodes n = gui.context.marked;
      for(int i = 0; i < n.size(); ++i) {
        if(i > 0) sb.append(',');
        sb.append(openPre(n, i));
      }
      gui.context.marked = new Nodes(n.data);
      gui.context.copied = null;
      gui.context.focused = -1;
      gui.execute(new XQuery("delete nodes (" + sb + ')'));
    }

    @Override
    public void refresh(final GUI gui, final AbstractButton b) {
      // disallow deletion of empty node set or root node
      b.setEnabled(updatable(gui.context.marked));
    }
  },

  /** Inserts new nodes. */
  C_INSERT(NEW + DOTS, "", H_NEW_NODE, true, false) {
    @Override
    public void execute(final GUI gui) {
      final Nodes n = gui.context.marked;
      final DialogInsert insert = new DialogInsert(gui);
      if(!insert.ok()) return;

      final StringList sl = insert.result;
      final NodeType type = ANode.type(insert.kind);
      String item = Token.string(type.string()) +
          " { " + quote(sl.get(0)) + " }";

      if(type == NodeType.ATT || type == NodeType.PI) {
        item += " { " + quote(sl.get(1)) + " }";
      } else if(type == NodeType.ELM) {
        item += " { () }";
      }

      gui.context.copied = null;
      gui.execute(new XQuery("insert node " + item + " into " + openPre(n, 0)));
    }

    @Override
    public void refresh(final GUI gui, final AbstractButton b) {
      b.setEnabled(updatable(gui.context.marked,
          Data.ATTR, Data.PI, Data.COMM, Data.TEXT));
    }
  },

  /** Opens a dialog to edit the currently marked nodes. */
  C_EDIT(EDIT + DOTS, "", H_EDIT, true, false) {
    @Override
    public void execute(final GUI gui) {
      final Nodes n = gui.context.marked;
      final DialogEdit edit = new DialogEdit(gui, n.list[0]);
      if(!edit.ok()) return;

      String rename = null;
      String replace = null;
      final int k = edit.kind;
      if(k == Data.ELEM || k == Data.PI || k == Data.ATTR) {
        rename = edit.result.get(0);
        if(k != Data.ELEM) replace = edit.result.get(1);
      } else {
        replace = edit.result.get(0);
      }

      if(rename != null) gui.execute(new XQuery("rename node " +
        openPre(n, 0) + " as " + quote(rename)));
      if(replace != null) gui.execute(new XQuery("replace value of node " +
        openPre(n, 0) + " with " + quote(replace)));
    }

    @Override
    public void refresh(final GUI gui, final AbstractButton b) {
      b.setEnabled(updatable(gui.context.marked, Data.DOC));
    }
  },

  /** Filters the currently marked nodes. */
  C_FILTER(FILTER_SELECTED, "", H_FILTER_SELECTED, true, false) {
    @Override
    public void execute(final GUI gui) {
      final Context ctx = gui.context;
      Nodes marked = ctx.marked;
      if(marked.size() == 0) {
        final int pre = gui.context.focused;
        if(pre == -1) return;
        marked = new Nodes(pre, ctx.data());
      }
      gui.notify.context(marked, false, null);
    }

    @Override
    public void refresh(final GUI gui, final AbstractButton b) {
      final Nodes marked = gui.context.marked;
      b.setEnabled(marked != null && marked.size() != 0);
    }
  },

  /** Shows the XQuery view. */
  C_SHOWEDITOR(EDITOR, "% E", H_EDITOR, false, true) {
    @Override
    public void execute(final GUI gui) {
      gui.gprop.invert(GUIProp.SHOWEDITOR);
      gui.layoutViews();
    }

    @Override
    public void refresh(final GUI gui, final AbstractButton b) {
      super.refresh(gui, b);
      b.setSelected(gui.gprop.is(GUIProp.SHOWEDITOR));
    }
  },

  /** Shows info. */
  C_SHOWINFO(QUERY_INFO, "% I", H_QUERY_INFO, false, true) {
    @Override
    public void execute(final GUI gui) {
      gui.gprop.invert(GUIProp.SHOWINFO);
      gui.layoutViews();
    }

    @Override
    public void refresh(final GUI gui, final AbstractButton b) {
      super.refresh(gui, b);
      b.setSelected(gui.gprop.is(GUIProp.SHOWINFO));
    }
  },

  /* VIEW MENU */

  /** Shows the buttons. */
  C_SHOWBUTTONS(BUTTONS, null, H_BUTTONS, false, true) {
    @Override
    public void execute(final GUI gui) {
      gui.gprop.invert(GUIProp.SHOWBUTTONS);
      gui.updateControl(gui.buttons, gui.gprop.is(GUIProp.SHOWBUTTONS),
          BorderLayout.CENTER);
    }

    @Override
    public void refresh(final GUI gui, final AbstractButton b) {
      super.refresh(gui, b);
      b.setSelected(gui.gprop.is(GUIProp.SHOWBUTTONS));
    }
  },

  /** Show Input Field. */
  C_SHOWINPUT(INPUT_BAR, null, H_INPUT_BAR, false, true) {
    @Override
    public void execute(final GUI gui) {
      gui.updateControl(gui.nav, gui.gprop.invert(GUIProp.SHOWINPUT),
          BorderLayout.SOUTH);
    }

    @Override
    public void refresh(final GUI gui, final AbstractButton b) {
      super.refresh(gui, b);
      b.setSelected(gui.gprop.is(GUIProp.SHOWINPUT));
    }
  },

  /** Shows the status bar. */
  C_SHOWSTATUS(STATUS_BAR, null, H_STATUS_BAR, false, true) {
    @Override
    public void execute(final GUI gui) {
      gui.updateControl(gui.status, gui.gprop.invert(GUIProp.SHOWSTATUS),
          BorderLayout.SOUTH);
    }

    @Override
    public void refresh(final GUI gui, final AbstractButton b) {
      super.refresh(gui, b);
      b.setSelected(gui.gprop.is(GUIProp.SHOWSTATUS));
    }
  },

  /** Shows the text view. */
  C_SHOWTEXT(TEXT, "% 1", H_TEXT, false, true) {
    @Override
    public void execute(final GUI gui) {
      gui.gprop.invert(GUIProp.SHOWTEXT);
      gui.layoutViews();
    }

    @Override
    public void refresh(final GUI gui, final AbstractButton b) {
      super.refresh(gui, b);
      b.setSelected(gui.gprop.is(GUIProp.SHOWTEXT));
    }
  },

  /** Shows the map. */
  C_SHOWMAP(MAP, "% 2", H_MAP, true, true) {
    @Override
    public void execute(final GUI gui) {
      gui.gprop.invert(GUIProp.SHOWMAP);
      gui.layoutViews();
    }

    @Override
    public void refresh(final GUI gui, final AbstractButton b) {
      super.refresh(gui, b);
      b.setSelected(gui.gprop.is(GUIProp.SHOWMAP));
    }
  },

  /** Shows the tree view. */
  C_SHOWTREE(TREE, "% 3", H_TREE, true, true) {
    @Override
    public void execute(final GUI gui) {
      gui.gprop.invert(GUIProp.SHOWTREE);
      gui.layoutViews();
    }

    @Override
    public void refresh(final GUI gui, final AbstractButton b) {
      super.refresh(gui, b);
      b.setSelected(gui.gprop.is(GUIProp.SHOWTREE));
    }
  },

  /** Shows the tree view. */
  C_SHOWFOLDER(FOLDER, "% 4", H_FOLDER, true, true) {
    @Override
    public void execute(final GUI gui) {
      gui.gprop.invert(GUIProp.SHOWFOLDER);
      gui.layoutViews();
    }

    @Override
    public void refresh(final GUI gui, final AbstractButton b) {
      super.refresh(gui, b);
      b.setSelected(gui.gprop.is(GUIProp.SHOWFOLDER));
    }
  },

  /** Shows the plot view. */
  C_SHOWPLOT(PLOT, "% 5", H_PLOT, true, true) {
    @Override
    public void execute(final GUI gui) {
      gui.gprop.invert(GUIProp.SHOWPLOT);
      gui.layoutViews();
    }

    @Override
    public void refresh(final GUI gui, final AbstractButton b) {
      super.refresh(gui, b);
      b.setSelected(gui.gprop.is(GUIProp.SHOWPLOT));
    }
  },

  /** Shows the table view. */
  C_SHOWTABLE(TABLE, "% 6", H_TABLE, true, true) {
    @Override
    public void execute(final GUI gui) {
      gui.gprop.invert(GUIProp.SHOWTABLE);
      gui.layoutViews();
    }

    @Override
    public void refresh(final GUI gui, final AbstractButton b) {
      super.refresh(gui, b);
      b.setSelected(gui.gprop.is(GUIProp.SHOWTABLE));
    }
  },

  /** Shows the explorer view. */
  C_SHOWEXPLORE(EXPLORER, "% 7", H_EXPLORER, true, true) {
    @Override
    public void execute(final GUI gui) {
      gui.gprop.invert(GUIProp.SHOWEXPLORE);
      gui.layoutViews();
    }

    @Override
    public void refresh(final GUI gui, final AbstractButton b) {
      super.refresh(gui, b);
      b.setSelected(gui.gprop.is(GUIProp.SHOWEXPLORE));
    }
  },

  /** Fullscreen mode. */
  C_FULL(FULLSCREEN, Prop.MAC ? "% shift F" : "F11", H_FULLSCREEN,
      false, true) {
    @Override
    public void execute(final GUI gui) {
      gui.fullscreen();
    }

    @Override
    public void refresh(final GUI gui, final AbstractButton b) {
      super.refresh(gui, b);
      b.setSelected(gui.fullscreen);
    }
  },

  /* OPTION MENU */

  /** Realtime execution on/off. */
  C_RTEXEC(RT_EXECUCTION, null, H_RT_EXECUTION, false, true) {
    @Override
    public void execute(final GUI gui) {
      gui.gprop.invert(GUIProp.EXECRT);
      gui.refreshControls();
      gui.notify.layout();
    }

    @Override
    public void refresh(final GUI gui, final AbstractButton b) {
      super.refresh(gui, b);
      b.setSelected(gui.gprop.is(GUIProp.EXECRT));
    }
  },

  /** Realtime filtering on/off. */
  C_RTFILTER(RT_FILTERING, null, H_RT_FILTERING, true, true) {
    @Override
    public void execute(final GUI gui) {
      final boolean rt = gui.gprop.invert(GUIProp.FILTERRT);
      gui.refreshControls();
      gui.notify.layout();

      final Context ctx = gui.context;
      final boolean root = ctx.root();
      if(!rt) {
        if(!root) {
          gui.notify.context(new Nodes(0, ctx.data()), true, null);
          gui.notify.mark(ctx.current(), null);
        }
      } else {
        if(root) {
          gui.notify.mark(new Nodes(ctx.data()), null);
        } else {
          final Nodes mark = ctx.marked;
          ctx.marked = new Nodes(ctx.data());
          gui.notify.context(mark, true, null);
        }
      }
    }

    @Override
    public void refresh(final GUI gui, final AbstractButton b) {
      super.refresh(gui, b);
      b.setSelected(gui.gprop.is(GUIProp.FILTERRT));
    }
  },

  /** Color schema. */
  C_COLOR(COLORS + DOTS, null, H_COLORS, false, false) {
    @Override
    public void execute(final GUI gui) {
      new DialogColors(gui);
    }
  },

  /** Changes the fonts. */
  C_FONTS(FONTS_D, null, H_FONTS, false, false) {
    @Override
    public void execute(final GUI gui) {
      new DialogFonts(gui);
    }
  },

  /** Map layout. */
  C_MAPLAYOUT(MAP_LAYOUT_D, null, H_MAP_LAYOUT, true, false) {
    @Override
    public void execute(final GUI gui) {
      new DialogMapLayout(gui);
    }
  },

  /** TreeView options. */
  C_TREEOPTIONS(TREE_OPTIONS_D, null, H_TREE_OPTIONS, true, false) {
    @Override
    public void execute(final GUI gui) {
      new DialogTreeOptions(gui);
    }
  },

  /** Shows a preference dialog. */
  C_PREFS(PREFERENCES + DOTS, Prop.MAC ? "% COMMA" : "% P",
      H_PREFERENCES, false, false) {
    @Override
    public void execute(final GUI gui) {
      new DialogPrefs(gui);
    }
  },

  /* HELP MENU */

  /** Shows the documentation web page. */
  C_HELP(HELP, "F1", H_HELP, false, false) {
    @Override
    public void execute(final GUI gui) {
      Dialog.browse(gui, DOC_URL);
    }
  },

  /** Opens the community web page. */
  C_COMMUNITY(COMMUNITY, null, H_COMMUNITY, false, false) {
    @Override
    public void execute(final GUI gui) {
      Dialog.browse(gui, COMMUNITY_URL);
    }
  },

  /** Opens the update web page. */
  C_UPDATES(CHECK_FOR_UPDATES, null, H_UPDATES, false, false) {
    @Override
    public void execute(final GUI gui) {
      Dialog.browse(gui, UPDATE_URL);
    }
  },

  /** Shows the "about" information. */
  C_ABOUT(ABOUT + DOTS, null, H_ABOUT, false, false) {
    @Override
    public void execute(final GUI gui) {
      new DialogAbout(gui);
    }
  },

  /* BROWSE COMMANDS */

  /** Goes one step back. */
  C_GOBACK(GO_BACK, "alt LEFT", GO_BACK, true, false) {
    @Override
    public void execute(final GUI gui) {
      gui.notify.hist(false);
    }

    @Override
    public void refresh(final GUI gui, final AbstractButton b) {
      final String tt = gui.notify.tooltip(true);
      b.setEnabled(tt != null);
      b.setToolTipText(tt != null && tt.isEmpty() ? GO_BACK : tt);
    }
  },

  /** Goes one step forward. */
  C_GOFORWARD(GO_FORWARD, "alt RIGHT", GO_FORWARD, true, false) {
    @Override
    public void execute(final GUI gui) {
      gui.notify.hist(true);
    }

    @Override
    public void refresh(final GUI gui, final AbstractButton b) {
      final String tt = gui.notify.tooltip(false);
      b.setEnabled(tt != null);
      b.setToolTipText(tt != null && tt.isEmpty() ? GO_FORWARD : tt);
    }
  },

  /** Goes one level up. */
  C_GOUP(GO_UP, "alt UP", H_GO_UP, true, false) {
    @Override
    public void execute(final GUI gui) {
      // skip operation for root context
      final Context ctx = gui.context;
      if(ctx.root()) return;
      // check if all nodes are document nodes
      boolean doc = true;
      final Data data = ctx.data();
      for(final int pre : ctx.current().list) doc &= data.kind(pre) == Data.DOC;
      if(doc) {
        // if yes, jump to database root
        ctx.update();
        gui.notify.context(ctx.current(), false, null);
      } else {
        // otherwise, jump to parent nodes
        gui.execute(new Cs(".."));
      }
    }

    @Override
    public void refresh(final GUI gui, final AbstractButton b) {
      b.setEnabled(!gui.gprop.is(GUIProp.FILTERRT) &&
          gui.context.data() != null && !gui.context.root());
    }
  },

  /** Goes to the root node. */
  C_GOHOME(GO_HOME, "alt HOME", H_GO_HOME, true, false) {
    @Override
    public void execute(final GUI gui) {
      // skip operation for root context
      final Context ctx = gui.context;
      if(ctx.root()) return;
      // jump to database root
      ctx.update();
      gui.notify.context(ctx.current(), false, null);
    }

    @Override
    public void refresh(final GUI gui, final AbstractButton b) {
      b.setEnabled(gui.context.data() != null && !gui.context.root());
    }
  },

  /** Displays the root node in the text view. */
  C_HOME(GO_HOME, null, H_GO_HOME, true, false) {
    @Override
    public void execute(final GUI gui) {
      gui.execute(new XQuery("/"));
    }
  };

  /** States if the command needs a data reference. */
  private final boolean data;
  /** Menu entry. */
  private final String entry;
  /** Key shortcut. */
  private final String key;
  /** Help string. */
  private final String help;
  /** Flag for commands that can be (un)checked. */
  private final boolean checked;

  /**
   * Constructor.
   * @param e text of the menu item
   * @param k key shortcut
   * @param h help string
   * @param d data reference flag
   * @param c checked flag
   */
  GUICommands(final String e, final String k, final String h, final boolean d,
      final boolean c) {
    entry = e;
    key = k;
    help = h;
    data = d;
    checked = c;
  }

  @Override
  public void refresh(final GUI gui, final AbstractButton b) {
    b.setEnabled(!data || gui.context.data() != null);
  }

  @Override
  public final boolean checked() { return checked; }

  @Override
  public String help() { return help; }

  @Override
  public String label() { return entry; }

  @Override
  public String key() { return key; }

  // STATIC METHODS ===========================================================

  /**
   * Checks if data can be updated.
   * @param n node instance
   * @param no disallowed node types
   * @return result of check
   */
  static boolean updatable(final Nodes n, final int... no) {
    if(n == null || (no.length == 0 ? n.size() < 1 : n.size() != 1))
      return false;

    final int k = n.data.kind(n.list[0]);
    for(final int i : no) if(k == i) return false;
    return true;
  }

  /**
   * Returns a quoted string.
   * @param s string to encode
   * @return quoted string
   */
  static String quote(final String s) {
    return '"' + s.replaceAll("\"", "&quot;") + '"';
  }

  /**
   * Returns a database function for the first node in a node set.
   * @param n node set
   * @param i offset
   * @return function string
   */
  static String openPre(final Nodes n, final int i) {
    return Function._DB_OPEN_PRE.get(null, Str.get(n.data.meta.name),
        Int.get(n.list[i])).toString();
  }
}
