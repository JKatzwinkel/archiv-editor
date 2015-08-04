package org.bbaw.pdr.ae.repositoryconnection.view;


import java.util.ArrayList;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IProgressMonitorWithBlocking;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.MultiStatus;
import org.eclipse.jface.dialogs.ProgressMonitorDialog;
import org.eclipse.jface.dialogs.TitleAreaDialog;
import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.jface.viewers.ITableLabelProvider;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Table;
import org.eclipse.swt.widgets.TableColumn;
import org.eclipse.swt.widgets.TableItem;
import org.eclipse.swt.widgets.Text;
import org.eclipse.swt.widgets.Tree;
import org.eclipse.swt.widgets.TreeColumn;

public class RepoUpdateStatusDialog extends TitleAreaDialog {
	
	private IStatus status;
	
	private TreeViewer statusTreeViewer;
	
	private String message;
	
	private String[] lvls = new String[]{"OK", "INFO", "WARNING", "ERROR", "ERROR"};
	
	
	public RepoUpdateStatusDialog(Shell parent, IStatus status, String message) {
		super(parent);
		this.status = status;
		this.message = message;
	}

	@Override
	public void create() {
		super.create();
		this.setTitle("Update Status Report");
		this.setMessage(message);
	}
	
	@Override
	protected Control createDialogArea(Composite parent) {
		Composite dialogAreaComp = (Composite)super.createDialogArea(parent);
		
		Composite statusComp = new Composite(dialogAreaComp, SWT.NONE);
		statusComp.setLayout(new GridLayout());
		
		GridData gd = new GridData(SWT.FILL, 0, true, false, 2, 1);
		statusComp.setLayoutData(gd);
		
		if (status.getMessage() != null && status.getMessage().length() > 0) {
			Label lbl = new Label(statusComp, SWT.NONE);
			lbl.setText(status.getMessage());
			lbl.setLayoutData(gd);
		}
		
		createStatusArea(dialogAreaComp);
		
		return dialogAreaComp;
	}
	
	
	private Composite createStatusArea(Composite parent) {
		Composite statusListComp = new Composite(parent, SWT.BORDER);
		statusListComp.setLayout(new GridLayout());
		
		GridData gd = new GridData(SWT.FILL, SWT.FILL, true, true, 2, 1);
		statusListComp.setLayoutData(gd);
		
		Tree statusTree = new Tree(statusListComp, SWT.BORDER | SWT.H_SCROLL | SWT.V_SCROLL);
		statusTree.setLinesVisible(true);
		statusTree.setHeaderVisible(true);
		statusTree.setLayoutData(gd);
		
		statusTreeViewer = new TreeViewer(statusTree);

		
		TreeColumn statusColumn = new TreeColumn(statusTree, SWT.LEFT);
		statusColumn.setText("Task");
		statusColumn.setAlignment(SWT.LEFT);
		statusColumn.setWidth(450);
		TreeColumn detailsColumn = new TreeColumn(statusTree, SWT.LEFT);
		detailsColumn.setText("Status");
		detailsColumn.setWidth(300);
		
		statusTreeViewer.setContentProvider(new StatusTreeContentProvider());
		statusTreeViewer.setLabelProvider(new StatusTableLabelProvider());
		
		statusTreeViewer.setInput(status.getChildren());
		statusTreeViewer.expandToLevel(1);
		
		return statusListComp;
	}

	@Override
	protected boolean isResizable() {
		return true;
	}
	
	class StatusTreeContentProvider implements ITreeContentProvider {

		@Override
		public void dispose() {}

		@Override
		public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {}

		@Override
		public Object[] getElements(Object inputElement) {
			//return new Object[]{status};
			return status.getChildren();
		}

		@Override
		public Object[] getChildren(Object parentElement) {
			if (parentElement instanceof IStatus) {
				if (((IStatus)parentElement).isMultiStatus()) {
					ArrayList<Object> children = new ArrayList<Object>();
					if (((IStatus)parentElement).getException() != null)
						children.add(((IStatus)parentElement).getException());
					for (IStatus child : ((IStatus)parentElement).getChildren())
						children.add(child);
					return children.toArray();
				} else if (((IStatus)parentElement).getException() != null)
					return new Throwable[]{((IStatus)parentElement).getException()};
			} else if (parentElement instanceof Throwable)
				if (((Throwable)parentElement).getCause() != null)
					return new Throwable[]{((Throwable)parentElement).getCause()};
			return new Object[0];
		}

		@Override
		public Object getParent(Object element) {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public boolean hasChildren(Object element) {
			if (element instanceof IStatus) {
				if (((IStatus)element).isMultiStatus()) {
					return ((IStatus)element).getChildren().length > 0;
				} else return (((IStatus)element).getException() != null);
			} else if (element instanceof Throwable)
				return ((Throwable)element).getCause() != null;
			return false;
		}
		
	}
	
	class StatusTableLabelProvider implements ITableLabelProvider {

		@Override
		public void addListener(ILabelProviderListener listener) {}

		@Override
		public void dispose() {}

		@Override
		public boolean isLabelProperty(Object element, String property) {
			return false;
		}

		@Override
		public void removeListener(ILabelProviderListener listener) {}

		@Override
		public Image getColumnImage(Object element, int columnIndex) {
			return null;
		}

		@Override
		public String getColumnText(Object element, int columnIndex) {
			if (columnIndex < 1) {
				if (element instanceof IStatus) {
					return ((IStatus)element).getMessage();
				} else if (element instanceof Throwable) {
					String text = ((Throwable)element).getClass().getName() + "\n";
					for (StackTraceElement ste : ((Throwable)element).getStackTrace() )
						text += " "+ste+"\n";
					return text;
				}	
			} else 
				if (element instanceof IStatus) {
					String text = lvls[((IStatus)element).getSeverity()];
					if (((IStatus)element).getException() != null)
						text += ": " + ((IStatus)element).getException().getClass().getName();
					return text;
				} else if (element instanceof Throwable) 
					return ((Throwable)element).getMessage();
			return null;
		}
		
	}
	
}
