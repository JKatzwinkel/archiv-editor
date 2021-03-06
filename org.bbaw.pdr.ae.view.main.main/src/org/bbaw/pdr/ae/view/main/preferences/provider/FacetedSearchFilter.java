/**
 * This file is part of Archiv-Editor.
 * 
 * The software Archiv-Editor serves as a client user interface for working with
 * the Person Data Repository. See: pdr.bbaw.de
 * 
 * The software Archiv-Editor was developed at the Berlin-Brandenburg Academy
 * of Sciences and Humanities, Jägerstr. 22/23, D-10117 Berlin.
 * www.bbaw.de
 * 
 * Copyright (C) 2010-2013  Berlin-Brandenburg Academy
 * of Sciences and Humanities
 * 
 * The software Archiv-Editor was developed by @author: Christoph Plutte.
 * 
 * Archiv-Editor is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * Archiv-Editor is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with Archiv-Editor.  
 * If not, see <http://www.gnu.org/licenses/lgpl-3.0.html>.
 */
package org.bbaw.pdr.ae.view.main.preferences.provider;

import java.util.ArrayList;

import org.bbaw.pdr.ae.config.model.ConfigData;
import org.bbaw.pdr.ae.config.model.ConfigItem;
import org.bbaw.pdr.ae.config.model.ConfigTreeNode;
import org.bbaw.pdr.ae.control.facade.Facade;
import org.bbaw.pdr.ae.control.interfaces.AMainSearcher;
import org.bbaw.pdr.ae.view.main.preferences.FacetedSearchPage;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerFilter;

/**
 * The Class FacetedSearchFilter.
 * @author Christoph Plutte
 */
public class FacetedSearchFilter extends ViewerFilter
{

	/** The faceted search page. */
	private FacetedSearchPage _facetedSearchPage;

	/** The selected items. */
	private ArrayList<ConfigItem> _selectedItems = new ArrayList<ConfigItem>();

	/** The rejected items. */
	private ArrayList<ConfigItem> _rejectedItems = new ArrayList<ConfigItem>();

	/** The main searcher. */
	private AMainSearcher _mainSearcher = Facade.getInstanz().getMainSearcher();

	/**
	 * Instantiates a new faceted search filter.
	 * @param facetedSearchPage the faceted search page
	 */
	public FacetedSearchFilter(final FacetedSearchPage facetedSearchPage)
	{
		this._facetedSearchPage = facetedSearchPage;
	}

	@Override
	public final boolean select(final Viewer viewer, final Object parentElement, final Object element)
	{
		ConfigTreeNode tn = (ConfigTreeNode) element;
		ConfigData cd = tn.getConfigData();
		if (cd instanceof ConfigItem)
		{
			ConfigItem ci = (ConfigItem) cd;

			if (_selectedItems.contains(ci))
			{
				return true;
			}
			else if (_rejectedItems.contains(ci))
			{
				return false;
			}

			String[] facets = null;
			if (_facetedSearchPage.getFacetProposals().containsKey(ci.getValue()))
			{
				tn.setSelected(true);
			}
			if (ci.getPos().equals("type"))
			{
				try
				{
					facets = _mainSearcher.getFacets(
							"tagging", ci.getParent().getValue().substring(5), ci.getValue(), null, //$NON-NLS-1$
							null);
				}
				catch (Exception e)
				{
					// TODO Auto-generated catch block
					e.printStackTrace();
				}

			}
			else if (ci.getPos().equals("subtype"))
			{
				try
				{
					facets = _mainSearcher.getFacets("tagging", ((ConfigItem) ci.getParent()).getParent().getValue()
							.substring(5), ci.getParent().getValue(), ci.getValue(), //$NON-NLS-1$
							null);
				}
				catch (Exception e)
				{
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
			}
			else if (ci.getPos().equals("role"))
			{
				try
				{
					facets = _mainSearcher.getFacets("tagging",
							((ConfigItem) ((ConfigItem) ci.getParent()).getParent()).getParent().getValue()
									.substring(5), ((ConfigItem) ci.getParent()).getParent().getValue(), ci.getParent()
									.getValue(), ci.getValue() //$NON-NLS-1$
							);
				}
				catch (Exception e)
				{
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
			}
			if (facets != null && facets.length > 0)
			{
				_selectedItems.add(ci);
				return true;
			}
			else
			{
				_rejectedItems.add(ci);
				return false;
			}
		}
		return true;
	}

}
