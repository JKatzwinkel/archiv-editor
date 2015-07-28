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
/*
 * @author: Christoph Plutte
 */
package org.bbaw.pdr.ae.control.datahandling.xqj.internal;

import java.io.ByteArrayInputStream;
import java.io.InputStream;
import java.io.StringReader;
import java.io.StringWriter;
import java.io.UnsupportedEncodingException;
import java.util.Arrays;
import java.util.Collections;
import java.util.Date;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.TreeSet;
import java.util.Vector;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import javax.xml.parsers.SAXParser;
import javax.xml.parsers.SAXParserFactory;
import javax.xml.stream.XMLStreamException;
import javax.xml.transform.Source;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerConfigurationException;
import javax.xml.transform.TransformerException;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.sax.SAXSource;
import javax.xml.transform.stream.StreamResult;
import javax.xml.transform.stream.StreamSource;
import javax.xml.validation.Schema;
import javax.xml.validation.SchemaFactory;
import javax.xml.validation.Validator;
import javax.xml.xquery.XQConnection;
import javax.xml.xquery.XQException;
import javax.xml.xquery.XQPreparedExpression;
import javax.xml.xquery.XQResultSequence;

import org.bbaw.pdr.ae.common.AEConstants;
import org.bbaw.pdr.ae.common.CommonActivator;
import org.bbaw.pdr.ae.config.core.ConfigXMLProcessor;
import org.bbaw.pdr.ae.config.core.DataDescSaxHandler;
import org.bbaw.pdr.ae.config.model.DatatypeDesc;
import org.bbaw.pdr.ae.control.core.PDRObjectDisplayNameProcessor;
import org.bbaw.pdr.ae.control.core.UserXMLProcessor;
import org.bbaw.pdr.ae.control.core.XMLProcessor;
import org.bbaw.pdr.ae.control.datahandling.xqj.config.ConfigManager;
import org.bbaw.pdr.ae.control.facade.Facade;
import org.bbaw.pdr.ae.control.interfaces.IUpdateManager;
import org.bbaw.pdr.ae.control.saxHandler.AspectSaxHandler;
import org.bbaw.pdr.ae.control.saxHandler.PersonSaxHandler;
import org.bbaw.pdr.ae.control.saxHandler.ReferenceSaxHandler;
import org.bbaw.pdr.ae.db.basex711.DBConnector;
import org.bbaw.pdr.ae.metamodel.PdrId;
import org.bbaw.pdr.ae.model.Aspect;
import org.bbaw.pdr.ae.model.PdrObject;
import org.bbaw.pdr.ae.model.Person;
import org.bbaw.pdr.ae.model.ReferenceMods;
import org.bbaw.pdr.ae.model.User;
import org.bbaw.pdr.ae.model.view.PDRObjectsConflict;
import org.bbaw.pdr.ae.repositoryconnection.view.UpdateConflictDialog;
import org.bbaw.pdr.allies.client.Configuration;
import org.bbaw.pdr.allies.client.IDRange;
import org.bbaw.pdr.allies.client.Identifier;
import org.bbaw.pdr.allies.client.PDRType;
import org.bbaw.pdr.allies.client.Repository;
import org.bbaw.pdr.allies.client.Utilities;
import org.bbaw.pdr.allies.error.InvalidIdentifierException;
import org.bbaw.pdr.allies.error.PDRAlliesClientException;
import org.eclipse.core.runtime.ILog;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.Status;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.progress.UIJob;
import org.xml.sax.Attributes;
import org.xml.sax.InputSource;
import org.xml.sax.SAXException;
import org.xml.sax.XMLReader;
import org.xml.sax.helpers.XMLFilterImpl;
import org.xml.sax.helpers.XMLReaderFactory;

/**
 * The Class RepositoryUpdateManager.
 * @author Christoph Plutte
 */
public class RepositoryUpdateManager implements IUpdateManager
{

	/** The db con. */
	private DBConnector _dbCon = DBConnector.getInstance();

	/** The repository id. */
	private int _repositoryId;

	/** The project id. */
	private int _projectId;

	/** The _facade. */
	private Facade _facade = Facade.getInstanz();

	/** The main searcher. */
	private MainSearcher _mainSearcher = new MainSearcher();

	/** The _xml proc. */
	private XMLProcessor _xmlProc = new XMLProcessor();

	/** The _user manager. */
	private UserManager _userManager = new UserManager();

	/** The _db manager. */
	private DBManager _dbManager = new DBManager();

	/** The _config manager. */
	private ConfigManager _configManager = new ConfigManager();

	/** The _id service. */
	private PdrIdService _idService = new PdrIdService();

	/** The conflicting rep aspects. */
	private Vector<String> _conflictingRepAspects = null;

	/** The conflicting rep persons. */
	private Vector<String> _conflictingRepPersons = null;

	/** The conflicting rep references. */
	private Vector<String> _conflictingRepReferences = null;

	/** The revision pattern. */
	private Pattern _revisionPattern = Pattern
			.compile("ref=\"\\d\\\" timestamp=\"\\d{4}\\-\\d{2}\\-\\d{2}T\\d{2}\\:\\d{2}\\:\\d{2}");

	/** The NEWOBJECT s_ packag e_ size. */
	private static final int NEWOBJECTS_PACKAGE_SIZE = 50;

	/** The MODIFIEDOBJECT s_ packag e_ size. */
	private static final int MODIFIEDOBJECTS_PACKAGE_SIZE = 50;

	/** package size. */
	private static final int PACKAGE_SIZE = 249;

	/** The MA x_ objec t_ number. */
	private static final int MAX_OBJECT_NUMBER = 99999999;
	/** Logger. */
	private static ILog iLogger = AEConstants.ILOGGER;
	/** status. */
	private IStatus log;

	private Validator aspectXMLValidator;

	private Validator personXMLValidator;

	private Validator userXMLValidator;

	private Validator referenceXMLValidator;

	/** instance of PDRObjectDisplayNameProcessor. */
	private PDRObjectDisplayNameProcessor _pdrDisplayNameProc = new PDRObjectDisplayNameProcessor();
	/**
	 * Takes a list of objects (which have been created locally after the most recent repo sync, i.e. which have only local IDs so far),
	 * a map of local to global IDs retrieved by the server, and an ID to find the global mapping for.
	 * Appends the hopefully found global ID for the specified ID and appends it to the passed vector of
	 * resolved global IDs, which is then returned.  
	 * @param objects updated objects.
	 * @param id id to find global mapping for
	 * @param idMap map of ids from repository
	 * @param begin begin index
	 * @param modifiedIds modified ids
	 * @return vector of modified ids
	 * @throws InvalidIdentifierException exc.
	 */
	private Vector<String> checkModfiedIds(final Vector<String> objects, final Identifier id,
			final Map<Identifier, Identifier> idMap, final int begin, final Vector<String> modifiedIds)
			throws InvalidIdentifierException {
		// System.out.println("checkModfiedIds");
		log(1, "Look up persistent global ID for local object "+id+" based on ID mapping provided by remote repo, amongst "+(objects.size()-begin)+" objects");
		//log(1, "Number of global IDs collectd so far: "+modifiedIds.size());
		for (int i = 0; i <= begin && i < objects.size(); i++) { // XXX wie bitte?
			String s = objects.get(i);
			if (s.contains(id.toString())) {
				Identifier oldId = new Identifier(extractPdrId(s));
				Identifier newId = idMap.get(oldId); // look up persistent global ID mapping for old ID/local ID 
				if (newId != null && !modifiedIds.contains(newId.toString())) {
					modifiedIds.add(newId.toString());
					log(1, "inserting modified obj oldid " + oldId.toString() + " new " + newId.toString());
				}
			}
		}
		//log(1, "Updated number of global IDs for locally new objects: "+modifiedIds.size());
		return modifiedIds;
	}

	/**
	 * checks if updated version from repository is really younger than the
	 * local one.
	 * @param repo version from repository
	 * @param col collection
	 * @param name id.
	 * @return true if repository version not older than local one
	 * @throws Exception
	 */
	private boolean checkVersions(final String repo, final String col, final String name) throws Exception {
		// System.out.println("checking version repo " + repo);
		String local = null;
		String logmsg; 
		try	{
			//System.out.println("checking version col " + col + " name " + name);
			// XXX klappt natuerlich nicht bei mods objekten, bei denen die revision im recordInfo? stehen soll
			local = _mainSearcher.searchObjectString(col, name);
			logmsg = "Compare object versions:\nlocal:  " + local+"\nremote: "+repo;
		} catch (XQException e)	{
			log(2, "local Object retrieval failed for "+name+" ("+col+")", e);
			return true;
		}
		boolean repoNewer = true;
		Date localLastDate = null;
		Date repoLastDate = null;
		if (local != null) {
			Matcher m = _revisionPattern.matcher(local);
			Vector<Date> revDates = new Vector<Date>();
			while (m.find()) 
				try {
					revDates.add(AEConstants.ADMINDATE_FORMAT.parse(m.group().split("timestamp=\"")[1]));
				} catch (Exception e) {
					// failed to parse revision timestamp
					// TODO: throw exception?
				}
			if (!revDates.isEmpty())
				localLastDate = Collections.max(revDates);
			if (repo != null) {
				revDates.clear();
				m = _revisionPattern.matcher(repo);
				while (m.find())
					try {
						revDates.add(AEConstants.ADMINDATE_FORMAT.parse(m.group().split("timestamp=\"")[1]));
					} catch  (Exception e) {
						// failed to parse revision timestamp
					}
				if (!revDates.isEmpty())
					repoLastDate = Collections.max(revDates);
			} else {// return false if repo object is null
				log(2, logmsg+"\nRemote object is null, hence not newer");
				repoNewer = false;
			}
			// return false if most recent repo object revision is not more recent than local object's
			// or if remote object revision could not be retrieved
			if (repoLastDate != null) {
				if (localLastDate != null && !repoLastDate.after(localLastDate))
					repoNewer = false;
			} else 
				repoNewer = false;
		} else // return true if local version is null, as we want to download remote version then
			repoNewer = true;
		log(1, logmsg+"\nTimestamps of latest revisions: local: "+localLastDate+", remote: "+repoLastDate+"\nRemote version newer: "+repoNewer);
		// return true if local object could not be retrieved or remote object is newer
		return repoNewer;
	}

	/**
	 * extracts pdrid from object xml string.
	 * @param objectString object xml as string
	 * @return pdrid
	 */
	static private String extractPdrId(final String objectString)
	{

		Matcher m = AEConstants.PDR_ID_PATTERN.matcher(objectString);
		String id = null;
		if (m.find())
		{
			id = m.group();
		}
		// objectString = objectString.split("<record")[0];
		//
		// // System.out.println("objectString " + objectString);
		// String id = objectString.split("id=\"")[1];
		// id = id.substring(0, 23);
		// System.out.println(id);
		return id;
	}

	/**
	 * Gets the modified aspects.
	 * <p>Obtains a list of IDs of modified aspects from {@link PdrIdService},
	 * looks up the corresponding XML serializations using {@link MainSearcher},
	 * removes aodl ns prefixes and returns the results.</p>
	 * @return the modified aspects
	 * @throws XQException the xQ exception
	 * @throws XMLStreamException the xML stream exception
	 */
	private Vector<String> getModifiedAspects() throws Exception
	{
		Vector<String> modifiedIds = _idService.getModifiedAspectIds();
		Vector<String> modifiedAspects = new Vector<String>(modifiedIds.size());
		String aspectString;

		for (String id : modifiedIds)
		{
			aspectString = _mainSearcher.searchObjectString("aspect", id);
			aspectString = removeAspectPrefixes(aspectString);
			// System.out.println("replacing aodls: " + modifiedAspects);
			String newStr = aspectString;
			try
			{
				newStr = new String(aspectString.getBytes("UTF-8"), "UTF-8");
			}
			catch (UnsupportedEncodingException e)
			{
				log = new Status(IStatus.INFO, Activator.PLUGIN_ID, "Exception ", e);
				iLogger.log(log);
				e.printStackTrace();
			}
			modifiedAspects.add(newStr);
		}
		return modifiedAspects;
	}

	/**
	 * Try to get a list of the remote's category providers. Use local providers
	 * on failure. Proceed to query remote repo for each provider's respective classification categories.
	 * Save those classification categories to local DB.
	 * @throws Exception
	 */
	private void getModifiedConfig(final IProgressMonitor monitor) throws Exception {
		// XXX sollten wir hier nicht mal irgendwo ne exception werfen?
		synchronized (_dbCon) {
			monitor.beginTask("Request list of remote classification providers", 1);
			List<String> providers = null;
			try {
				log(1, "Attempt to retrieve remote category providers");
				providers = Utilities.getCategoryProviders();
				log(0, "Retrieved "+providers.size()+" category providers from repo");
				monitor.worked(1);
			} catch (Exception e2) {
				log(2, "Retrieval of remote category providers failed: ", e2);
			}
			if (providers == null) {
				log(1, "No category providers could be retrieved. Use local provider information instead.");
				providers = new Vector<String>();
				for (String provider :  _facade.getConfigs().keySet())
					providers.add(provider);
				monitor.worked(1);
			}
			monitor.beginTask("Synchronize local classification configurations", providers.size());
			for (String provider :  providers) {
				String modifiedConfig = null;
				try {
					log(1, "Try to retrieve remote categories configuration for provider "+provider);
					monitor.subTask("Request classification configuration for provider "+provider);
					modifiedConfig = Utilities.getCategories(provider);
					if (modifiedConfig != null && modifiedConfig.trim().length() > 0
							&& !modifiedConfig.contains("file not found")) {
						SAXParserFactory factory = SAXParserFactory.newInstance();
						ConfigManager configManager = new ConfigManager();
						try {
							log(1, "Set up XML and SAX processors for configuration element");
							// init XML/SAX processors for category configuration element read-in
							InputStream xmlInput = new ByteArrayInputStream(modifiedConfig.getBytes("UTF-8"));
							SAXParser saxParser = factory.newSAXParser();
							// XXX custom parser for configration elements
							DataDescSaxHandler handler = new DataDescSaxHandler(configManager);
							XMLReader reader = saxParser.getXMLReader();
							try {
								log(1, "Initialize XML reader");
								// Turn on validation
								reader.setFeature("http://xml.org/sax/features/validation", true); //$NON-NLS-1$
								// Ensure namespace processing is on (the default)
								reader.setFeature("http://xml.org/sax/features/namespaces", true); //$NON-NLS-1$
							} catch (Exception e) {
								log(2, "Parser could not be initialized: ", e);
							}
	
							log(1, "Parse XML serialization of modified configuration");
							saxParser.parse(xmlInput, handler);
						} catch (Throwable err)	{
							log(2, "Import of category configuration object XML failed: ", err);
						}
	
						DatatypeDesc dtd = configManager.getDatatypeDesc();
						if (dtd != null && dtd.isValid()) {
							if (dtd.getProvider() != null
									&& dtd.getProvider().equals(
											Platform.getPreferencesService()
													.getString(CommonActivator.PLUGIN_ID, "PRIMARY_SEMANTIC_PROVIDER",
															AEConstants.CLASSIFICATION_AUTHORITY, null)))
							{
								// TODO: huh?
							}
							try	{
								log(1, "Save configurations to local database");
								_configManager.saveConfig(dtd);
							} catch (Exception e)	{
								log(2, "Saving configurations to local database failed: ", e);
							}
						}
					}
					monitor.worked(1);
				} catch (PDRAlliesClientException e1) {
					log = new Status(2, Activator.PLUGIN_ID, "ALLIES Exception during remote configuration retrieval for provider "+provider, e1);
					iLogger.log(log);
					e1.printStackTrace();
				}
			}
		}
	}

	/**
	 * Gets the modified persons.
	 * I.e. get IDs from DB coll pdrPo/modified/id from {@link PdrIdService},
	 * retrieve object XML stored from DB using {@link MainSearcher#searchObjectString(String, String)}
	 * with coll name parameter "person", remove podl namespace prefixes from XML,
	 * return all you've got. 
	 * @return the modified persons
	 * @throws XQException the xQ exception
	 * @throws XMLStreamException the xML stream exception
	 */
	private Vector<String> getModifiedPersons() throws Exception {
		Vector<String> modifiedIds = _idService.getModifiedPersonIds(); // get locally modified person objects (XML)
		log(1, "Number of person objects with local modifications = "+modifiedIds.size());
		Vector<String> modifiedPersons = new Vector<String>(modifiedIds.size());
		String personString;

		for (String id : modifiedIds) {
			personString = _mainSearcher.searchObjectString("person", id);
			try {
				personString = removePersonPrefix(personString); // remove podl nx prefixes in XML
				modifiedPersons.add(personString);
			} catch (Exception e) {
				if (personString == null)
					log(2, "Person not found");
				log(2, "Couldn't load modified person object ["+id+"] from local DB: ", e);
			}
		}
		return modifiedPersons;
	}

	/**
	 * Gets the modified references.
	 * I.e. get IDs in DB collection pdrRo/modified/id from {@link PdrIdService},
	 * get local DB XML for those from {@link MainSearcher#searchObjectString(String, String)} 
	 * with "reference" as collection name parameter and return those XML strings.
	 * rodl ns prefixes are not removed from XML
	 * @return the modified references
	 * @throws XQException the xQ exception
	 * @throws XMLStreamException the xML stream exception
	 */
	private Vector<String> getModifiedReferences() throws Exception
	{
		Vector<String> modifiedIds = _idService.getModifiedReferenceIds();
		Vector<String> modifiedRefs = new Vector<String>(modifiedIds.size());
		String refString;
		for (String id : modifiedIds)
		{
			refString = _mainSearcher.searchObjectString("reference", id);
			modifiedRefs.add(refString);
		}
		return modifiedRefs;
	}

	/**
	 * Gets the modified users.
	 * I.e. query Ids from pdrUo/modified/id DB coll, look users up in
	 * uodl namespace in DB via {@link UserManager#getUserById(String)},
	 * serialize into XML, remove uodl namespace prefixes from XML,
	 * return list of XML strings. 
	 * @return the modified users
	 * @throws XQException the xQ exception
	 * @throws XMLStreamException the xML stream exception
	 */
	private Vector<String> getModifiedUsers() throws Exception
	{
		Vector<String> modifiedIds = _idService.getModifiedUserIds();
		Vector<String> modifiedUsers = new Vector<String>(modifiedIds.size());
		User u;
		UserXMLProcessor userXMLProc = new UserXMLProcessor();
		// Pattern openP = Pattern.compile("<podl:");
		// Pattern closeP = Pattern.compile("<\\/podl:");
		// Matcher m = openP.matcher(personString);
		// m.replaceAll("<");
		// m = closeP.matcher(personString);
		// m.replaceAll("</");
		String userString;
		for (String id : modifiedIds)
		{
			u = _userManager.getUserById(id);
			if (u != null)
			{
				userString = userXMLProc.writeToXML(u);
				userString = removeUserPrefix(userString); // oudl ns prefixes are removed
				modifiedUsers.add(userString);
			}
		}
		return modifiedUsers;
	}

	/**
	 * Gets the new users, i.e. queries all IDs in DB collection pdrUo/new/id and
	 * uses a {@link UserXMLProcessor} to generate XML serialization of the objects
	 * which a {@link UserManager} provides for those IDs.
	 * Btw. uodl namespace prefixes in XML tags are apparently being removed before return.
	 * 
	 * @return the new users
	 * @throws XQException the xQ exception
	 * @throws XMLStreamException the xML stream exception
	 */
	private Vector<String> getNewUsers() throws Exception
	{
		Vector<String> modifiedIds = _idService.getNewUserIds();
		Vector<String> modifiedUsers = new Vector<String>(modifiedIds.size());
		User u;
		UserXMLProcessor userXMLProc = new UserXMLProcessor();
		// Pattern openP = Pattern.compile("<podl:");
		// Pattern closeP = Pattern.compile("<\\/podl:");
		// Matcher m = openP.matcher(personString);
		// m.replaceAll("<");
		// m = closeP.matcher(personString);
		// m.replaceAll("</");
		String userString;
		for (String id : modifiedIds)
		{
			u = _userManager.getUserById(id);
			if (u != null && u.getPdrId() != null)
			{
				userString = userXMLProc.writeToXML(u);
				userString = removeUserPrefix(userString);
				modifiedUsers.add(userString);
			}

		}
		return modifiedUsers;
	}

	/**
	 * Handle objects conflicts.
	 * <p>
	 * Processes the three update conflicts lists populated earlier during the calls of
	 * {@link #injestModifiedReferences(IProgressMonitor)}, {@link #injestModifiedPersons(IProgressMonitor)}
	 * and {@link #injestModifiedAspects(IProgressMonitor)}.
	 * Update conflict lists contain entire objects.
	 * XML from update conflicts lists is being parsed and {@link PdrObject} subclass instances are
	 * created for them. Local counterpart is obtained from {@link Facade}.
	 * A {@link PDRObjectsConflict} instance is created for each item in the update conflict lists,
	 * and initialized with both the remote and the local {@link PdrObject} instances.
	 * </p><p>
	 * Then an {@link UpdateConflictDialog} is opened and if it returns 0, 
	 * {@link PdrIdService#clearAllUpdateStates()} is called. Regardless of
	 * the result of this call, {@link #insertConflictingObjects(Vector, IProgressMonitor)}
	 * gets called three times, one for every list of {@link PDRObjectsConflict} instances.
	 * Finally, {@link Facade#refreshAllData()} is invoked.
	 * </p>
	 * @param monitor the monitor
	 */
	private void handleObjectsConflicts(final IProgressMonitor monitor)
	{
		UIJob job = new UIJob("Update Conflict Handling") {
			 @Override
			 public IStatus runInUIThread(IProgressMonitor monitor) {
				 String id;
					PDRObjectsConflict oConflict;
					Vector<PDRObjectsConflict> conAspects = null;
					Vector<PDRObjectsConflict> conPersons = null;
					Vector<PDRObjectsConflict> conReferences = null;
					InputStream is;
					SAXParserFactory factory = SAXParserFactory.newInstance();
					SAXParser saxParser = null;
					try	{
						saxParser = factory.newSAXParser();
					} catch (Exception e1) {
						log = new Status(IStatus.WARNING, Activator.PLUGIN_ID, "Init of SAX parser failed ", e1);
						iLogger.log(log);
						e1.printStackTrace();
					}

					// PREPARE ASPECT CONFLICT RESOLUTION
					if (_conflictingRepAspects != null && !_conflictingRepAspects.isEmpty()) {
						log(1, "Number of aspect object conflicts: "+_conflictingRepAspects.size());
						AspectSaxHandler handler = new AspectSaxHandler(new PdrObject[]	{}, monitor);
						conAspects = new Vector<PDRObjectsConflict>(_conflictingRepAspects.size());
						for (String s : _conflictingRepAspects)	{
							id = extractPdrId(s);
							if (saxParser != null) {
								try {
									is = new ByteArrayInputStream(s.getBytes("UTF-8"));
									saxParser.parse(is, handler);
									oConflict = new PDRObjectsConflict();
									// TODO: koennte schiefgehen, wenn resultobject mehrere sind!
									Aspect parsedAspect = (Aspect) handler.getResultObject();
									if (parsedAspect != null) {
										_pdrDisplayNameProc.processDisplayName(parsedAspect);
										oConflict.setRepositoryObject(parsedAspect);
									}
									parsedAspect = null;
									oConflict.setLocalObject(_facade.getAspect(new PdrId(id)));
									conAspects.add(oConflict);
									log(1, "Prepare conflict resolution for aspect "+id);
								} catch (Exception e) {
									log(2, "Conflict res preparation failed for aspect "+id, e);
								}
							}
						}
						log(1, "Scheduled "+conAspects.size()+" resolutions. Total number of conflicts: "+_conflictingRepAspects);
					}
					
					// PREPARE PERSON CONFLICT RESOLUTION
					if (_conflictingRepPersons != null && !_conflictingRepPersons.isEmpty()) {
						log(1, "Number of person object conflicts: "+_conflictingRepPersons.size());
						conPersons = new Vector<PDRObjectsConflict>(_conflictingRepPersons.size());
						PersonSaxHandler handler = new PersonSaxHandler();
						for (String s : _conflictingRepPersons)	{
							id = extractPdrId(s);
							if (saxParser != null)	{
								try	{
									is = new ByteArrayInputStream(s.getBytes("UTF-8"));
									saxParser.parse(is, handler);
									oConflict = new PDRObjectsConflict();
									Object o = handler.getResultObject();
									Person parsedPerson = null;
									if (o instanceof Person) {
										parsedPerson = (Person) o;
									} else { // aha: problem mehrerer rueckgaben wird behandelt!
										Map<PdrId, Person> persons = (Map<PdrId, Person>) o;
										for (Person p : persons.values())
										{
											parsedPerson = p;
											break;
										}
									}
									if (parsedPerson != null) {
										_pdrDisplayNameProc.processDisplayName(parsedPerson);
										oConflict.setRepositoryObject(parsedPerson);
									}
									parsedPerson = null;
									oConflict.setLocalObject(_facade.getPdrObject(new PdrId(id)));
									conPersons.add(oConflict);
									log(1, "Prepare conflict resolution for person "+id);
								} catch (Exception e) {
									log(2, "Conflict resolution prep failed for person "+id, e);
								}
							}
							log(1, "Scheduled "+conPersons.size()+" resolutions. Total number of conflicts: "+_conflictingRepPersons);
						}
					}
					
					// PREPARE REFERENCE CONFLICT RESOLUTION
					if (_conflictingRepReferences != null && !_conflictingRepReferences.isEmpty()) {
					     // XXX this might fix nullpointer problem of issue 3132
						PDRObjectDisplayNameProcessor dnp = new PDRObjectDisplayNameProcessor();
						log(1, "Number of reference object conflicts: "+_conflictingRepReferences.size());
						conReferences = new Vector<PDRObjectsConflict>(_conflictingRepReferences.size());
						ReferenceSaxHandler handler = new ReferenceSaxHandler();
						for (String s : _conflictingRepReferences) {
							id = extractPdrId(s);
							if (saxParser != null) {
								try	{
									is = new ByteArrayInputStream(s.getBytes("UTF-8"));
									saxParser.parse(is, handler);
									oConflict = new PDRObjectsConflict();
									ReferenceMods parsedReference = (ReferenceMods) handler.getResultObject();
									if (parsedReference != null) {
										/*_pdrDisplayNameProc.processDisplayName(parsedReference);
										_pdrDisplayNameProc.processDisplayNameLong(parsedReference);
										oConflict.setRepositoryObject(parsedReference);*/
										dnp.processDisplayName(parsedReference); // XXX this produces a long display name and possibly fixes nullpointer exception in conflict dialog
									    oConflict.setRepositoryObject(parsedReference); // FIXME: updateconflictdialog fails because of nullpointer when probably this object's longdisplayname is accessed
									    // TODO: does this error (longdisplayname, conflict dialog) still occur as of v2.3.10??
									}
									parsedReference = null;
									oConflict.setLocalObject(_facade.getReference(new PdrId(id)));
									conReferences.add(oConflict);
									log(1, "Prepare conflict resolution for reference "+id);
								} catch (Exception e) {
									log(2, "Conflict resolution prep failed for reference "+id, e);
								}
							}
							log(1, "Scheduled "+conReferences.size()+" resolutions. Total number of conflicts: "+_conflictingRepReferences);
						}
					}

					// conflict resolution dialog
					log(1, "Open Conflict Resolution Dialog.");
					IWorkbench workbench = PlatformUI.getWorkbench();
					Display display = workbench.getDisplay();
					Shell shell = new Shell(display);
					UpdateConflictDialog dialog = new UpdateConflictDialog(shell, conAspects, conPersons, conReferences); //$NON-NLS-1$
					if (dialog.open() == 0)  {// FIXME dialog GUI creation does not go well because of messed up reference obj
						// TODO: is the above FIXME still relevant as of v2.3.10?
						// TODO: test mods object conflicts!!!
					 
						int totalWork = 0;
						if (conAspects != null) totalWork = conAspects.size();
						if (conPersons != null) totalWork = totalWork + conPersons.size();
						if (conReferences != null) totalWork = totalWork + conReferences.size();
						monitor.beginTask("Resolving Update Conflicts. Number of Objects: " + totalWork, totalWork);
						
						try {
							_idService.clearAllUpdateStates();
						} catch (Exception e) {
							log(2, "Could not clear update states of local objects: ", e);
						}
						if (conAspects != null && !conAspects.isEmpty())
							try {
								// resolve aspects conflicts by either overwriting local or remote
								// version or by prosponing resolution
								insertConflictingObjects(conAspects, monitor);
							} catch (Exception e) {
								log(2, "Resolution of aspect object conflicts failed: ", e);
							} 
						 if (conPersons != null && !conPersons.isEmpty())
							 try {
								 // resolve PERSON conflicts by overwrite one way or another or by prosponing
								 insertConflictingObjects(conPersons, monitor);
							 } catch (Exception e) {
								 log(2, "Resolution of person object conflicts failed: ", e);
							 } 
						 if (conReferences != null && !conReferences.isEmpty())
							 try {
								 // resolve reference conflicts just like aspects and persons
								 insertConflictingObjects(conReferences, monitor);
							 } catch (Exception e) {
								log(2, "Resolution of reference object conflicts failed: ", e);
							 }
					 }
				// no matter how conflict dialog went:
				// refresh all pdr object information in facade; reload entirely from DB?
				_facade.refreshAllData();

				return Status.OK_STATUS;
			 }};
			 job.setUser(true);
//			 IJobManager manager = Job.getJobManager();
//			manager.currentJob().
			 job.schedule();
			 try {
				job.join();
			 } catch (InterruptedException e) {
				log = new Status(IStatus.WARNING, Activator.PLUGIN_ID, "Conflict resolution UI job failed: ", e);
				iLogger.log(log);
				e.printStackTrace();
			}
	}

	/**
	 * Injest modified aspects.
	 * <p>Seems to work exactly like {@link #injestModifiedReferences(IProgressMonitor)} and
	 * {@link #injestModifiedPersons(IProgressMonitor)}. aodl ns prefixes are removed from XMl.
	 * @param monitor the monitor
	 * @throws XQException the xQ exception
	 * @throws UnsupportedEncodingException the unsupported encoding exception
	 * @throws PDRAlliesClientException the pDR allies client exception
	 * @throws XMLStreamException the xML stream exception
	 */
	private void injestModifiedAspects(final IProgressMonitor monitor) throws Exception
	{
		synchronized (_dbCon) {
			_conflictingRepAspects = new Vector<String>();
			List<String> subConflRepAspects = new Vector<String>();
			List<String> aspects = getModifiedAspects(); // without aodl prefixes
			if (aspects.size() == 0)
				return;
			log(1, "Begin to ingest "+aspects.size()+" modified aspect objects from local DB into remote repo");
			monitor.beginTask("Ingesting Modified Aspects into Repository. Number of Objects: " + aspects.size(),
					aspects.size());

			int counter = 0;
			int begin = 0;
			int end = (aspects.size() > MODIFIEDOBJECTS_PACKAGE_SIZE) ? MODIFIEDOBJECTS_PACKAGE_SIZE : aspects.size();  
			Vector<String> subAspects = new Vector<String>(end);
			for (int i = begin; i < end; i++) {
				String xml = aspects.get(i);
				if (!isValidXMLAspect(xml)) {
					String xml2 = makeValidXMLAspect(xml);
					if (xml2 != null) {
						subAspects.add(xml);
					} else
						log(2, "Invalid aspect: "+xml);
				} else
					subAspects.add(xml);
			}
			// push until done
			while (subAspects != null && !subAspects.isEmpty())	{
				log(1, "Push "+subAspects.size()+" aspect objects to project ["+_projectId+"] at repo ["+_repositoryId+"]");
				for (String xml : subAspects)
					System.out.println(xml);
				subConflRepAspects = Repository.modifyObjects(_repositoryId, _projectId, subAspects, false);
				if (subConflRepAspects != null && !subConflRepAspects.isEmpty()) {
					log(1, ""+subConflRepAspects.size()+" new conflicts");
					_conflictingRepAspects.addAll(subConflRepAspects);
				}
				monitor.worked(subAspects.size());
				begin = end;
				end = (aspects.size() > MODIFIEDOBJECTS_PACKAGE_SIZE + end) ? (end + MODIFIEDOBJECTS_PACKAGE_SIZE) :aspects.size();
				counter += subAspects.size();
				subAspects.clear();

				for (int i = begin; i < end; i++) {
					String xml = aspects.get(i);
					if (!isValidXMLAspect(xml)) {
						String xml2 = makeValidXMLAspect(xml);
						if (xml2 != null) {
							subAspects.add(xml);
						} else
							log(2, "Invalid aspect: "+xml);
					} else
						subAspects.add(xml);
				}
			}
			log(0, "Done pushing modified aspects objects. Total number of pushed aspects: "+counter+" (modified aspects: "+aspects.size()+")");
		}
	}

	/**
	 * Injest modified config.
	 * <p>
	 * query object IDs in DB coll config/modified/id. Those are the configuration providers, apparently.
	 * Then iterate through all those config providers, retrieve some {@link DatatypeDesc} objects for them from
	 * a {@link ConfigManager}, which represent dltl XML schema, and sends them to the remote one after another
	 * by calling {@link Utilities#setCategories(String, String)}.
	 * </p>
	 * @throws XQException the xQ exception
	 * @throws UnsupportedEncodingException the unsupported encoding exception
	 * @throws PDRAlliesClientException the pDR allies client exception
	 * @throws XMLStreamException the xML stream exception
	 */
	private void injestModifiedConfig(final IProgressMonitor monitor) throws Exception
	{
		synchronized (_dbCon)
		{
			Vector<String> configProviders = _idService.getModifiedConfigs();
			// Vector<String> configs =
			// _configManager.getConfigs(configProviders);
			monitor.beginTask("Uploading local modifications to classification configurations. Number of Classification Providers: "+configProviders.size(), configProviders.size());
			// XXX anpassen
			for (String s : configProviders)
			{
				log(1, "Send category definition on server for locally modified provider "+s);
				DatatypeDesc dtd = _configManager.getDatatypeDesc(s);
				String configStr = new ConfigXMLProcessor().writeToXML(dtd);
				System.out.println("injestModifiedConfig() " + configStr);
				Utilities.setCategories(configStr, dtd.getProvider());
				monitor.worked(1);

			}
		}

	}

	/**
	 * Injest modified persons.
	 * <p>
	 * get XML of person objects registered as modified from DB.
	 * remove podl prefixes in XML.
	 * validate XML.
	 * Send XML list to server and save update conflict list it returns.
	 * </p>
	 * @param monitor the monitor
	 * @throws UnsupportedEncodingException the unsupported encoding exception
	 * @throws PDRAlliesClientException the pDR allies client exception
	 * @throws XQException the xQ exception
	 * @throws XMLStreamException the xML stream exception
	 */
	private void injestModifiedPersons(final IProgressMonitor monitor) throws Exception {
		// XXX: vielleicht die confligierenden objekte lieber als return value statt global?
		synchronized (_dbCon) {
			_conflictingRepPersons = new Vector<String>();
			List<String> subConflictingPersons = new Vector<String>();
			List<String> persons = getModifiedPersons();
			if (persons.size() == 0)
				return;
			log(1, "Begin to ingest "+persons.size()+" modified person objects from local DB");
			monitor.beginTask("Ingesting Modified Persons into Repository. Number of Objects: " + persons.size(),
					persons.size());

			int counter = 0;
			int begin = 0;
			int end = (persons.size() > NEWOBJECTS_PACKAGE_SIZE) ? NEWOBJECTS_PACKAGE_SIZE : persons.size();
			
			Vector<String> subPersons = new Vector<String>(end);
			// iterate over first chunk of person objects
			for (int i = begin; i < end; i++) {
				String xml = persons.get(i);
				if (!isValidXMLPerson(xml)) {
					String xml2 = makeValidXMLPerson(xml);
					if (xml2 != null) {
						subPersons.add(xml2);
					} else
						log(2, "Invalid person object: "+xml);
				} else
					subPersons.add(xml);
			}
			
			// keep pushing and chunking until no modified person remains
			while (subPersons != null && !subPersons.isEmpty())	{
				log(1, "Push "+subPersons.size()+" person objects to project ["+_projectId+"] at repo ["+_repositoryId+"]");
				for (String xml : subPersons)
					System.out.println(xml);
				subConflictingPersons = Repository.modifyObjects(_repositoryId, _projectId, subPersons, false);
				if (subConflictingPersons != null && !subConflictingPersons.isEmpty()) {
					log(1, ""+subConflictingPersons.size()+" new conflicts");
					_conflictingRepPersons.addAll(subConflictingPersons);
				}
				monitor.worked(subPersons.size());
				// proceed to next chunk
				begin = end;
				end = (persons.size() > NEWOBJECTS_PACKAGE_SIZE+end) ? (end+NEWOBJECTS_PACKAGE_SIZE) : persons.size();
				counter += subPersons.size();
				subPersons.clear();

				for (int i = begin; i < end; i++) {
					String xml = persons.get(i);
					if (!isValidXMLPerson(xml)) {
						String xml2 = makeValidXMLPerson(xml);
						if (xml2 != null) {
							subPersons.add(xml2);
						} else
							log(2, "Invalid person object: "+xml);
					} else
						subPersons.add(xml);
				}
			}
			log(0, "Done pushing modified person objects. Total number of pushed persons: "+counter+" (modified persons: "+persons.size()+")");
		}
	}

	/**
	 * Injest modified references.
	 * <p>
	 * Get XML of modified references from DB
	 * Remove rodl/mods namespaces.
	 * Push XML to server using {@link Repository#modifyObjects(int, int, List, boolean)}
	 * save server response (list of conflicting objects) for later.
	 * </p> 
	 * @param monitor the monitor
	 * @throws UnsupportedEncodingException the unsupported encoding exception
	 * @throws PDRAlliesClientException the pDR allies client exception
	 * @throws XQException the xQ exception
	 * @throws XMLStreamException the xML stream exception
	 */
	private void injestModifiedReferences(final IProgressMonitor monitor) throws Exception {
		synchronized (_dbCon) {
			_conflictingRepReferences = new Vector<String>();

			List<String> subConflictingRefs = new Vector<String>();
			List<String> references = getModifiedReferences();
			if (references.size() == 0)
				return;
			log(1, "Loaded "+references.size()+" modified reference objects from local DB");
			monitor.beginTask("Ingesting Modified References into Repository. Number of Objects: " + references.size(),
					references.size());

			int counter = 0;
			int begin = 0;
			int end = (references.size() > NEWOBJECTS_PACKAGE_SIZE) ? NEWOBJECTS_PACKAGE_SIZE : references.size();
			// prepare first chunk of reference objects for submission
			Vector<String> subReferences = new Vector<String>(end);
			String ref;
			for (int i = begin; i < end; i++) {
				ref = references.get(i);
				ref = removeRefPrefix(ref); // remove mods ns prefixes XXX warum nicht in getmodifiedreferences?
				if (!isValidXMLReference(ref)) {
					String xml2 = makeValidXMLReference(ref);
					if (xml2 != null) {
						subReferences.add(xml2);
					} else
						log(2, "Invalid reference object: "+ref);
				} else
					subReferences.add(ref);
			}
			
			// keep on pushing and chunking until all reference objects have been sent to repo
			while (subReferences != null && !subReferences.isEmpty()) {
				// FIXME: SOAP fault
				log(1, "Push "+subReferences.size()+" reference objects to project ["+_projectId+"] at repo ["+_repositoryId+"]");
				for (String r : subReferences) {
					System.out.println(r);
					Matcher m = this.pdrModsLinkPattern.matcher(r);
					while (m.find())
						System.out.println("RelatedItem: "+m.group(1));
				}
				subConflictingRefs = Repository.modifyObjects(_repositoryId, _projectId, subReferences, false);
				if (subConflictingRefs != null && !subConflictingRefs.isEmpty()) {
					log(1, ""+subConflictingRefs.size()+" new conflicts");
					_conflictingRepReferences.addAll(subConflictingRefs);
				}
				monitor.worked(subReferences.size());
				// proceed to next chunk
				begin = end;
				end = (references.size() > NEWOBJECTS_PACKAGE_SIZE+end) ? (end+NEWOBJECTS_PACKAGE_SIZE) : references.size();   
				counter += subReferences.size();
				subReferences.clear();

				for (int i = begin; i < end; i++) {
					ref = references.get(i);
					ref = removeRefPrefix(ref);
					if (!isValidXMLReference(ref)) {
						String xml2 = makeValidXMLReference(ref);
						if (xml2 != null) {
							subReferences.add(xml2);
						} else
							log(2, "Invalid reference object: "+ref);
					} else
						subReferences.add(ref);
				}
			}
			log(0, "Done pushing modified reference objects. Total number of pushed references: "+counter);
		}
	}

	/**
	 * Injest modified users.
	 * <p>
	 * Get XML of users whose IDs are in pdrUo/modified/id DB collection.
	 * Send XML list to server by calling {@link Repository#modifyObjects(int, int, List, boolean)},
	 * with forced update flag set to true.
	 * Don't mind update conflict that might be returned by server.
	 * </p>  
	 * 
	 * @throws UnsupportedEncodingException the unsupported encoding exception
	 * @throws PDRAlliesClientException the pDR allies client exception
	 * @throws XQException the xQ exception
	 * @throws XMLStreamException the xML stream exception
	 */
	private final void injestModifiedUsers() throws Exception {
		synchronized (_dbCon) {
			Vector<String> users = getModifiedUsers(); // without uodl ns prefixes
			int counter = 0;
			int begin = 0;
			int end = (users.size() > MODIFIEDOBJECTS_PACKAGE_SIZE) ? MODIFIEDOBJECTS_PACKAGE_SIZE : users.size();
			Vector<String> subUsers = new Vector<String>(end);
			for (int i = begin; i < end; i++) {
				String xml = users.get(i);
				if (!isValidXMLUser(xml)) {
					String xml2 = makeValidXMLUser(xml);
					if (xml2 != null) {
						subUsers.add(xml2);
					} else
						log(2, "Invalid user object: "+xml);
				} else
					subUsers.add(xml);
			}
			
			// push and chunk until no user remains unknown to the remote
			while (subUsers != null && !subUsers.isEmpty()) {
				log(1, "Push "+subUsers.size()+" user objects to project ["+_projectId+"] at repo ["+_repositoryId+"]");
				Repository.modifyObjects(_repositoryId, _projectId, subUsers, true);
				// XXX: kein conflict handling???
				begin = end;
				end = (users.size() > MODIFIEDOBJECTS_PACKAGE_SIZE+end) ? (end + MODIFIEDOBJECTS_PACKAGE_SIZE) : users.size();  
				counter += subUsers.size();
				subUsers.clear();

				for (int i = begin; i < end; i++) {
					String xml = users.get(i);
					if (!isValidXMLUser(xml)) {
						String xml2 = makeValidXMLUser(xml);
						if (xml2 != null) {
							subUsers.add(xml2);
						} else
							log(2, "Invalid user object: "+xml);
					} else
						subUsers.add(xml);
				}
			}
			log(0, "Done pushing modified user objects. Total number of pushed users: "+counter);
		}
	}

	/**
	 * Take XML aspect object, extract ID, lookup actual aspect under ID,
	 * write aspect to XML. 
	 * @param xml
	 * @return
	 */
	private String makeValidXMLAspect(String xml) {
		// check input
		boolean isValid = isValidXMLAspect(xml);
		
		if (!isValid) {
			log(1, "Aspect XML is invalid:\n"+xml);
			String id = extractPdrId(xml);
			Aspect a = _facade.getAspect(new PdrId(id));
			String xml2 = "";
			try {
				xml2 = _xmlProc.writeToXML(a);
			} catch (XMLStreamException e) {
				log = new Status(IStatus.WARNING, Activator.PLUGIN_ID, "Failed to write XML for aspect "+a.getDisplayNameWithID(), e);
				iLogger.log(log);
				return null;
			}
			if (isValidXMLAspect(xml2)) {	
				try {
					synchronized (_dbCon) {
						_dbCon.store2DB(xml2, "aspect", id + ".xml", false);
						log(0, "saved " + id+".xml"+":\n"+xml2);
					}
					_dbCon.optimize("aspect");
					// XXX saveaspect wirft nullpointer bei dagmar siehe log vom 29.5.
					//_facade.saveAspect(a); // XXX bringt das ueberhaupt was wenn aspect nicht new oder dirty ist? Und ist dies vielleicht der grund fuer die doppelten aspecte in baseX? 
				} catch (Exception e) {
					log = new Status(IStatus.WARNING, Activator.PLUGIN_ID, "Failed to write aspect to DB: "+a.getDisplayNameWithID(), e);
					iLogger.log(log);
					return null;
				}
				return xml2;
			}
		} else
			return xml;
		return null;
	}
	
	private boolean isValidXMLAspect(String xml) {
		Source source = new StreamSource(new StringReader(xml));
		// check input
		boolean isValid = true;
		try {
			getAspectXMLValidator().validate(source);
		} catch (Exception e) {
			//log = new Status(IStatus.WARNING, Activator.PLUGIN_ID, "Invalid aspect xml exempted from synchronisation " + xml);
			//iLogger.log(log);
			//log = new Status(IStatus.INFO, Activator.PLUGIN_ID, "Exception ", e);
			//iLogger.log(log);
			isValid = false;
		}
		return isValid;
	}
	private Validator getAspectXMLValidator() {
		if (aspectXMLValidator == null)	{
			// build the schema
			SchemaFactory factory = SchemaFactory.newInstance("http://www.w3.org/2001/XMLSchema");
			InputStream stream = this.getClass().getClassLoader().getResourceAsStream("/schemas/aodl.xsd");
			Schema schema;
			Source schemaSource = new StreamSource(stream);
			try {
				schema = factory.newSchema(schemaSource);
				aspectXMLValidator = schema.newValidator();
			} catch (SAXException e) {
				log = new Status(IStatus.ERROR, Activator.PLUGIN_ID, "Unable to get aspect XML validator! ", e);iLogger.log(log);
			}
		}
		return aspectXMLValidator;
	}
	
	
	private boolean isValidXMLPerson(String xml) {
		Source source = new StreamSource(new StringReader(xml));
		// check input
		boolean isValid = true;
		try {
			getPersonXMLValidator().validate(source);
		} catch (Exception e) {
			/*log = new Status(IStatus.INFO, Activator.PLUGIN_ID, "Not valid person xml exempted from synchronisation " + xml);
			iLogger.log(log);
			log = new Status(IStatus.INFO, Activator.PLUGIN_ID, "Exception ", e);
			iLogger.log(log);*/
			isValid = false;
		}
		return isValid;
	}
	private String makeValidXMLPerson(String xml) {
		// check input
		boolean isValid = isValidXMLPerson(xml);
		if (!isValid) {
			String id = extractPdrId(xml);
			Person p = _facade.getPerson(new PdrId(id));
			String xml2 = "";
			try {
				xml2 = _xmlProc.writeToXML(p);
			} catch (XMLStreamException e) {
				log = new Status(IStatus.WARNING, Activator.PLUGIN_ID, "Failed to write person to XML: "+p.getDisplayNameWithID(), e);
				iLogger.log(log);
				return null;
			}
			if (isValidXMLPerson(xml2))	{
				try {
					_dbCon.store2DB(xml2, "person", id.toString() + ".xml", true);
					log = new Status(IStatus.INFO, Activator.PLUGIN_ID, "Saved object " + id.toString());
					//_facade.savePerson(p); // XXX geht schief nullpointer dagmar 19.5.
					//if (isValidXMLPerson(xml2))	{
					//}
				} catch (Exception e) {
					log = new Status(IStatus.WARNING, Activator.PLUGIN_ID, "Failed to  write person to DB "+p.getDisplayNameWithID(), e);
					iLogger.log(log);
					return null;
				}
				return xml2;
			}
		} else
			return xml;
		return null;
	}
	private Validator getPersonXMLValidator() {
		if (personXMLValidator == null)	{
			SchemaFactory factory = SchemaFactory.newInstance("http://www.w3.org/2001/XMLSchema");
			InputStream stream = this.getClass().getClassLoader().getResourceAsStream("/schemas/podl.xsd");
			Schema schema;
			Source schemaSource = new StreamSource(stream);
			try {
				schema = factory.newSchema(schemaSource);
				personXMLValidator = schema.newValidator();
			} catch (SAXException e) {
				log = new Status(IStatus.ERROR, Activator.PLUGIN_ID, "Failed to get podl XML validator ", e);
				iLogger.log(log);}
		}
		return personXMLValidator;
	}
	
	
	private boolean isValidXMLUser(String xml) {
		Source source = new StreamSource(new StringReader(xml));
		// check input
		boolean isValid = true;
		try {
		getUserXMLValidator().validate(source);
		} catch (Exception e) {
			log = new Status(IStatus.INFO, Activator.PLUGIN_ID, "Not valid user xml exempted from synchronisation " + xml);
			iLogger.log(log);
			log = new Status(IStatus.INFO, Activator.PLUGIN_ID, "Exception " + e);
			iLogger.log(log);
		isValid = false;
		}

		return isValid;
	}
	private String makeValidXMLUser(String xml) {
		// check input
		boolean isValid = isValidXMLUser(xml);
		
		if (!isValid)
		{
			String id = extractPdrId(xml);
			User u = null;
			try {
				u = _userManager.getUserById(id);
			} catch (Exception e1) {
				log = new Status(IStatus.INFO, Activator.PLUGIN_ID, "Exception ", e1);
				iLogger.log(log);
				return null;
			}
			
			String xml2 = "";
			try {
				UserXMLProcessor userXMLProc = new UserXMLProcessor();
				xml2 = userXMLProc.writeToXML(u);
			} catch (XMLStreamException e) {
				log = new Status(IStatus.INFO, Activator.PLUGIN_ID, "Exception ", e);
				iLogger.log(log);
				return null;
			}
			if (isValidXMLUser(xml2))
			{
				try {
					_userManager.saveUser(u);
					if (isValidXMLUser(xml2))
					{
						return xml2;
					}
				} catch (Exception e) {
					log = new Status(IStatus.INFO, Activator.PLUGIN_ID, "Exception ", e);
					iLogger.log(log);
				}
			}
		}
		else
		{
			return xml;
		}
		return null;
	}
	private Validator getUserXMLValidator() {
		if (userXMLValidator == null)
		{
			SchemaFactory factory = SchemaFactory.newInstance("http://www.w3.org/2001/XMLSchema");
			InputStream stream = this.getClass().getClassLoader().getResourceAsStream("/schemas/uodl.xsd");
			Schema schema;
			Source schemaSource = new StreamSource(stream);
			try {
				schema = factory.newSchema(schemaSource);
				userXMLValidator = schema.newValidator();

			} catch (SAXException e) {
				log = new Status(IStatus.INFO, Activator.PLUGIN_ID, "Exception ", e);
				iLogger.log(log);			}
		}
		return userXMLValidator;
	}
	
	
	private boolean isValidXMLReference(String xml) {
		Source source = new StreamSource(new StringReader(xml));
		// check input
		boolean isValid = true;
		try {
			getReferenceXMLValidator().validate(source);
		} catch (Exception e) {
			/*log = new Status(IStatus.INFO, Activator.PLUGIN_ID, "Not valid reference xml exempted from synchronisation " + xml);
			iLogger.log(log);
			log = new Status(IStatus.INFO, Activator.PLUGIN_ID, "Exception ", e);
			iLogger.log(log);*/
			System.out.println(xml);
			e.printStackTrace();
			isValid = false;
		}
		return isValid;
	}
	/**
	 * For a given PDR mods object XML serialization, check validity
	 * against corresponding XML schema (rodl_mods.xsd) and re-serialize
	 * object to XML in case of invalidity. On re-serialization, result is
	 * also saved to local DB in an attempt to overwrite possibly invalid
	 * local DB object representation.
	 * <p>Process is as follows:
	 * <ol><li>check validity of XML string using {@link #isValidXMLReference(String)}</li>
	 * <li>if invalid:
	 * 	<ol><li>extract pdr id string</li>
	 * 	<li>retrieve {@link ReferenceMods} object by id from {@link Facade#getReference(PdrId)}</li>
	 * 	<li>serialize to XML using {@link XMLProcessor}</li>
	 * 	<li>check validity of resulting XML, if valid, save to DB using {@link Facade#saveReference(ReferenceMods)}, return XML string
	 * Note: on re-serialization, xml elements will contain namespace prefixes</p>
	 * @param xml possibly invalid XML representation of PDR mods reference, containing PDR id attribute 
	 * @return hopefully valid XML
	 */
	private String makeValidXMLReference(String xml) {
		// check input
		boolean isValid = isValidXMLReference(xml);
		if (!isValid) {
			String id = extractPdrId(xml);
			ReferenceMods r = _facade.getReference(new PdrId(id));
			String xml2 = "";
			try {
				xml2 = _xmlProc.writeToXML(r);
			} catch (XMLStreamException e) {
				log = new Status(IStatus.WARNING, Activator.PLUGIN_ID, "Failed to write mods XML "+r.getDisplayNameWithID(), e);
				iLogger.log(log);
				return null;
			}
			if (isValidXMLReference(xml2))	{
				try {
					_dbCon.store2DB(xml2, "reference", id.toString() + ".xml", true);
					log = new Status(IStatus.INFO, Activator.PLUGIN_ID, "renameObject renaming done " + id.toString());
					// _facade.saveReference(r); // XXX nullpointer bei dagmar siehe log 19.5.
				} catch (Exception e) {
					log = new Status(IStatus.WARNING, Activator.PLUGIN_ID, "Failed to save mods ref to DB "+r.getDisplayNameWithID(), e);
					iLogger.log(log);
					return null;
				}
				return xml2;
			}
		} else
			return xml;
		return null;
	}
	private Validator getReferenceXMLValidator() {
		if (referenceXMLValidator == null) {
			SchemaFactory factory = SchemaFactory.newInstance("http://www.w3.org/2001/XMLSchema");
			InputStream stream = this.getClass().getClassLoader().getResourceAsStream("/schemas/rodl_mods.xsd");
			Schema schema;
			Source schemaSource = new StreamSource(stream);
			try {
				schema = factory.newSchema(schemaSource);
				referenceXMLValidator = schema.newValidator();
			} catch (SAXException e) {
				log = new Status(IStatus.ERROR, Activator.PLUGIN_ID, "Failed to get mods XML validator ", e);
				iLogger.log(log);			
			}
		}
		return referenceXMLValidator;
	}
	
	/**
	 * Takes given PDR object XML representation, determines type (reference, person, aspect)
	 * and ensures its validity by delegation to type-specific methods. Those methods
	 * re-serialize the represented object and save resulting XML to local DB. Resulting XML
	 * most likely contains namespace prefixes in all elements.
	 * @param xml XMl representation of object as a String
	 * @return potentially re-serialized, valid XML representation of object
	 * @see #makeValidXMLReference(String)
	 * @see #makeValidXMLPerson(String)
	 * @see #makeValidXMLAspect(String)
	 */
	private String makeValidPDRObjectXML(String xml) {
		PdrId id = new PdrId(extractPdrId(xml));
		if (id.getType().equals("pdrRo")) return removeRefPrefix(makeValidXMLReference(xml));
		if (id.getType().equals("pdrPo")) return removePersonPrefix(makeValidXMLPerson(xml));
		if (id.getType().equals("pdrAo")) return removeAspectPrefixes(makeValidXMLAspect(xml));
		log(2, "Didn't delegate XML validation/validization. Possibly invalid.");
		return xml;
	}
	
	/**
	 * Determines if XML is valid representation of {@link ReferenceMods}, {@link Person}
	 * or {@link Aspect}. Returns false if given XML represents no object type is not amongst these three. 
	 * @param xml
	 * @return true if validation was successful
	 */
	private boolean isValidPDRObjectXML(String xml) {
		PdrId id = new PdrId(extractPdrId(xml));
		if (id.getType().equals("pdrRo")) return isValidXMLReference(xml);
		if (id.getType().equals("pdrPo")) return isValidXMLPerson(xml);
		if (id.getType().equals("pdrAo")) return isValidXMLAspect(xml);
		log(2, "Didn't delegate XML validation. Possibly invalid.");
		return false;
	}
	

	/**
	 * Injest new config.
	 * @throws XQException the xQ exception
	 * @throws XMLStreamException the xML stream exception
	 * @throws UnsupportedEncodingException the unsupported encoding exception
	 * @throws PDRAlliesClientException the pDR allies client exception
	 */
	private void injestNewConfig() throws XQException, XMLStreamException, UnsupportedEncodingException,
			PDRAlliesClientException
	{
		// synchronized (dbCon)
		// {
		// Vector<String> configProviders = _idService.getNewConfigs();
		// Vector<String> configs = _configManager.getConfigs(configProviders);
		// //XXX anpassen
		// if (configs != null && !configs.isEmpty())
		// Repository.ingestObjects(repositoryId, projectId, configs);
		// }

	}

	/**
	 * Injest new users.
	 * <p>
	 * XML serialization of user objects whose IDs are in the local pdrUo/new/id DB collection
	 * is obtained via  {@link #getNewUsers()}.
	 * Object IDs are then extracted from those very XML strings which have themselves been just queried by ID.
	 * User objects are then divided into two sets, one for users to be ingested into remote, one for
	 * standard users with IDs lower than 10, which are expected to be present in every project.
	 * <strike>The collection of users to be ingested is being ingested first, the collection of standard users
	 * is ingested later in method {@link #checkAndInjestStandardUsers(Vector, String, String)},
	 * which does not process temp to persistent ID mapping returned by server.
	 * (To tell apart standard users from custom local users, their IDs are again extracted from
	 * XML strings using regular expressions...)</strike>
	 * Finally, persistent user IDs as returned from the server at XML ingest are propagated
	 * in the local DB.
	 * </p>
	 * @throws UnsupportedEncodingException the unsupported encoding exception
	 * @throws PDRAlliesClientException the pDR allies client exception
	 * @throws XQException the xQ exception
	 * @throws XMLStreamException the xML stream exception
	 * @throws InvalidIdentifierException the invalid identifier exception
	 */
	private final void injestNewUsers(String userId, String password) throws Exception
	{
		synchronized (_dbCon) {
			Vector<String> users = new Vector<String>();
			// filter user objects with inaccurate project ID
			for (String s : getNewUsers())
				if (extractPdrId(s).split("\\.")[2].equals(""+_projectId))
					users.add(s);
			if (users.size()<1) return;
			String logmsg="Begin ingesting new users from local DB into repo:"+users.size();
			for (String s : users)
				logmsg += "\n "+s.replaceAll("(\n|\t)", "");
			log(1, logmsg);
			int counter = 0;
			int begin = 0;
			int end = (users.size() > NEWOBJECTS_PACKAGE_SIZE) ? NEWOBJECTS_PACKAGE_SIZE : users.size(); 
			Vector<String> subUsers = new Vector<String>(end);
			Vector<String> modifiedUserIds = new Vector<String>();
			Vector<String> standardUsers = new Vector<String>(9);
			for (int i = begin; i < end; i++) {
				if (new Integer(extractPdrId(users.get(i)).substring(14)) <= 9)	{
					standardUsers.add(users.get(i));
				} else	{
					String xml = users.get(i);
					if (!isValidXMLUser(xml)) {
						String xml2 = makeValidXMLUser(xml);
						if (xml2 != null)
							subUsers.add(xml2);
					} else
						subUsers.add(xml);
				}
			}
			while (subUsers != null && !subUsers.isEmpty())	{
				logmsg = "Ingest "+subUsers.size()+" uodl objects to remote repo:";
				for (String s : subUsers)
					logmsg += "\n " + extractPdrId(s);
				log(1, logmsg);
				Map<Identifier, Identifier> idMap = Repository.ingestObjects(_repositoryId, _projectId, subUsers);
				if (!idMap.isEmpty()) {
					// System.out.println("size of map " + idMap.size());
					String newID;
					for (Identifier id : idMap.keySet()) {
						newID = idMap.get(id).toString();
						modifiedUserIds = checkModfiedIds(users, id, idMap, begin, modifiedUserIds);
						// renameObject(id, newID);
						resetObjectId(id, newID, 4);
					}
				}
	
				begin = end;
				end = (users.size() > NEWOBJECTS_PACKAGE_SIZE + end) ? end + NEWOBJECTS_PACKAGE_SIZE : users.size();
				counter += subUsers.size();
				subUsers.clear();
	
				for (int i = begin; i < end; i++) {
					if (new Integer(extractPdrId(users.get(i)).substring(14)) <= 9)	{
						standardUsers.add(users.get(i));
					} else	{
						String xml = users.get(i);
						if (!isValidXMLUser(xml)) {
							String xml2 = makeValidXMLUser(xml);
							if (xml2 != null)
								subUsers.add(xml2);
						} else
							subUsers.add(xml);
					}
				}
			}
			if (modifiedUserIds != null && !modifiedUserIds.isEmpty()) 
				_idService.insertIdModifiedObject(modifiedUserIds, "pdrUo");
			//if (!standardUsers.isEmpty()) 
				//checkAndInjestStandardUsers(standardUsers, userId, password);
		}
		log(0, "Done uploading new users");
	}

	/** matches relatedItem links (to new objects) in mods objects **/
	static private Pattern pdrModsLinkPattern = Pattern.compile("<.*?:?relatedItem.*?ID=\"(pdr[APRU]o\\.\\d{3}\\.\\d{3}\\.1\\d{8})\".*?>");
	/** matches inter (new) object references in aspect objects */
	static private String pdrAspectLinkTags = "(<relation[^>]*?object=\"|ana=\"|<reference[^>]*>)";
	static private Pattern pdrAspectLinkPattern = Pattern.compile(pdrAspectLinkTags+"(pdr[APRU]o\\.\\d{3}\\.\\d{3}\\.1\\d{8})");
	/** TODO matcher for person object XML */
	static private String pdrPersonLinkTags = "(<concurrence[^>]*person=\"|<reference[^>]*>)";
	static private Pattern pdrPersonLinkPattern = Pattern.compile(pdrPersonLinkTags+"(pdr[APRU]o\\.\\d{3}\\.\\d{3}\\.1\\d{8})");
	// TODO: aspect can be aspect_of of another aspect

	/**
	 * Searches XML string for references to other new local objects. Matched relations are
	 * <ul><li>in mods objects: relatedItem</li>
	 * <li>in aspects: relation object=, ana=, reference</li>
	 * <li>in person objects: TODO</li>
	 * </ul> 
	 * Make sure xml is without namespace prefixes!
	 * @param xml XML repr of object <i>without NS prefixes</i>
	 * @return
	 */
	static private Vector<String> findLinkedLocalObjects(String xml) {
		Vector<String> links = new Vector<String>();
		PdrId id = new PdrId(extractPdrId(xml)); // extract pdr id from xml
		if (id.getType().equals("pdrRo")) {	
			// find links in Mods object
			Matcher m = pdrModsLinkPattern.matcher(xml);
			while (m.find()) {
				String relid = m.group(1);
				//System.out.println("Mods objekt "+id+" references "+relid);
				links.add(relid);
			}
		} else if (id.getType().equals("pdrPo")) {
			Matcher m = pdrPersonLinkPattern.matcher(xml);
			while (m.find()) {
				String relid = m.group(2);
				//System.out.println("Person objekt "+id+" references "+relid);
				links.add(relid);
			}
		} else if (id.getType().equals("pdrAo")) {
			// find links in aspect object
			Matcher m = pdrAspectLinkPattern.matcher(xml);
			while (m.find()) {
				String relid = m.group(2);
				//System.out.println("Aspect objekt "+id+" references "+relid);
				links.add(relid);
			}
		}
		return links;
	}
	
	
	/**
	 * Ingests new reference, person and aspect objects (in this order) into remote repo.
	 * @param monitor
	 * @return
	 * @throws Exception
	 */
	private Vector<String> ingestNewPDRObjects(final IProgressMonitor monitor) throws Exception {
		synchronized (_dbCon) {
			// Ids of objects that couldn't be ingested */
			Set<String> failures = new TreeSet<String>();
			// XML repr of new local PDR objects as obtained from MainSearcher */
			Vector<String> newObjsXml =  new Vector<String>();
			// ids of new local PDR objects in whatever order local DB returned them*/
			Vector<String> newObjsIds = new Vector<String>();
			// this is a dictionary of new local objects which object ids reference and are hence dependent on
			HashMap<String, Vector<String>> dependencies = new HashMap<String, Vector<String>>();
			// this is a dictionary of transitive incoming links between new local objects. **/ 
			HashMap<String, Set<String>> dependingOn = new HashMap<String, Set<String>>();
			// retrieve new local objects from MainSearcher
			newObjsXml.addAll(_mainSearcher.getNewReferences());
			newObjsXml.addAll(_mainSearcher.getNewPersons());
			newObjsXml.addAll(_mainSearcher.getNewAspects());
			// extract PdrId from object XML, validate XML, prepare dependency dict
			for (String s : newObjsXml) {
				String id = extractPdrId(s); // extract pdr id from xml
				String xml = makeValidPDRObjectXML(s); // validate xml repr (and remove ns prefixes)
				if (xml != null) {
					newObjsIds.add(id);
					dependingOn.put(id, new TreeSet<String>());
				} else {
					log(2, "XML seems to be invalid, exempt from ingestion:\n"+xml);
					failures.add(id); // TODO: excempt dependent objects
				}
				// find and register dependencies of object
				dependencies.put(id, findLinkedLocalObjects(xml));
			}
			// generate dict of depending objects from dependency map, 
			for (String i : newObjsIds) 
				for (String d : dependencies.get(i))
					try {
						dependingOn.get(d).add(i);
					} catch (NullPointerException e) {
						log(2, "Object "+i+" references unknown object "+d);
					}
						
			// sequence of new objs Ids put in dependency-sensitive order
			Vector<String> objsIdqueue = new Vector<String>();
			// infer transitive dependencies, detect dependency loops
			// resolve dependencies
			for (String i : newObjsIds) {
				Set<String> dependents = new TreeSet<String>(dependingOn.get(i));
				boolean expanding = true;
				while (expanding) {
					for (String in : dependingOn.get(i)) // add all objs linking known dependencies as dependencies 
						dependents.addAll(dependingOn.get(in));
					expanding = (dependents.size()>dependingOn.get(i).size());
					dependingOn.put(i, new TreeSet<String>(dependents));		
				}
				// check for loops
				if (dependents.contains(i)) {
					log(2, "Detected object dependency loop at object "+i);
					// return all new local objects, all these objects failed to be ingested
					return newObjsIds;
				}
				// line up object id for ingestion
				objsIdqueue.add(i);
				// bring object ids in correct order
				// check dependents and move current obj queue position if necessary
				for (String in : dependingOn.get(i)) // go through all dependent objects
					if (objsIdqueue.contains(in)) { // if objects depending on current object is already in ingest queue, compare positions
						// queue position dependent obj
						int inqup = objsIdqueue.indexOf(in);
						// queue position current obj
						int qup = objsIdqueue.indexOf(i);
						// if linking obj is farther up front than dependent obj, place the latter ahead
						if (inqup < qup) {
							objsIdqueue.remove(qup);
							objsIdqueue.add(inqup, i);
							System.out.println("Put "+i+" ahead of "+in);
						}
					}
			}
			// TODO: jetzt sollten in failures eventuelle invalide objekte stehen; auf der grundlage
			// sollte man hier oder so die von diesen abhaengigen objekte ebenfalls rausfischen..!!!
			TreeSet<String> faildeps = new TreeSet<String>();
			for (String i : failures)
				faildeps.addAll(dependingOn.get(i));
			failures.addAll(faildeps);
				
			for (String i : objsIdqueue)
				System.out.println(i);
			//if (newObjsIds.size()>0)
				//return null;
			// ===== INGEST =====
			// pdr object types ingest sequence
			Vector<String> pdrTypes = new Vector<String>(Arrays.asList("pdrRo", "pdrPo", "pdrAo"));
			// now that ids of new local objects are in order, proceed to ingesting them in type-wise packets
			// for this we retrieve the object identified by the elements of the id queue from local DB
			monitor.beginTask("Ingesting new local objects into repository. Number of objects: " + newObjsIds.size(), newObjsIds.size());
			int counter = 0;

			// loop through pdr type ingest sequence
			for (String pdrType : pdrTypes) {
				log(0, "Ingest new local objects of type "+pdrType);
				// prepare packet of new objects for current type
				Vector<String> packet = new Vector<String>();
				for (String i : objsIdqueue)
					if (!failures.contains(i)) // exclude objects that would fail due to unmet dependencies
						if (pdrType.equals(i.substring(0, 5)))
							packet.add(_mainSearcher.getObjectXML(i));
				if (!packet.isEmpty()) {
					log(1, "Push "+packet.size()+" NEW "+pdrType+" objects to project ["+_projectId+"] at repo ["+_repositoryId+"]");				
					// list of persistent (global) IDs returned by server on ingest on local objects 
					Vector<String> persistentIds = new Vector<String>();
					//////////////////
					// attempt ingest
					//////////////////
					try {
						Map<Identifier, Identifier> idMap = Repository.ingestObjects(_repositoryId, _projectId, packet);
						// update local DB using the persistent ID the server returned
						for (Entry<Identifier, Identifier> idMapping : idMap.entrySet()) {
							persistentIds.add(idMapping.getValue().toString());
							// rewrite links to this object in all DB objects of dependent types
							resetObjectId(idMapping.getKey(), idMapping.getValue().toString(), 
									3-pdrTypes.indexOf(pdrType));
							counter ++;
							monitor.worked(1);
						}
						log(0, "Ingested "+counter+"/"+packet.size()+" "+pdrType+" new local objects.");
						// on success, remember persistent object id returned by server, (try to avoid using checkModifiedIds) 
						// rewrite local DB object index with new id, update all objects linking the old id
						// (call resetObjectId up to level 3), remove objects from local DB 'modified' collection
						// (IDService.insertIdModifiedObject)
						if (!persistentIds.isEmpty()) 
							_idService.insertIdModifiedObject(persistentIds, pdrType); // XXX stay alert: objects might still pop up as 'modified' later
						log(0, "server returned "+persistentIds.size()+" global IDs)");
					} catch (Exception e) {
						// if ingest fails regardless of thoughtful precautions, terminate ingest, return all queued objects
						// as failure list
						log(2, "Could not ingest/update new local objects (login as "+Configuration.getInstance().getPDRUserID()+" @ "+Configuration.getInstance().getAxis2BaseURL()+")", e);
						
						failures.addAll(packet);
						return new Vector<String>( failures );
					}
					monitor.worked(packet.size());
				}
			}
			
			
			log(0, "Done pushing NEW local objects. Total number of ingested objects: "+counter+"\n(out of "+newObjsXml.size()+" new objects");
			return new Vector<String>(failures);
		}
	}
	
	/**
	 * Injest new references.
	 * @param monitor the monitor
	 * @throws XQException the xQ exception
	 * @throws UnsupportedEncodingException the unsupported encoding exception
	 * @throws PDRAlliesClientException the pDR allies client exception
	 * @throws InvalidIdentifierException the invalid identifier exception
	 */
	private void injestNewReferences(final IProgressMonitor monitor) throws Exception
	{
		synchronized (_dbCon) {
			Vector<String> references = _mainSearcher.getNewReferences();
			if (references.size() == 0)
				return;
			log(1, "Begin ingest of "+references.size()+" NEW reference objects from local DB into remote repo");
			monitor.beginTask("Ingesting new References into Repository. Number of Objects: " + references.size(),
					references.size());
	
			int counter = 0;
			int begin = 0;
			int end = (references.size() > NEWOBJECTS_PACKAGE_SIZE) ? NEWOBJECTS_PACKAGE_SIZE : references.size();
			Vector<String> subReferences = new Vector<String>(end);
			Vector<String> modifiedReferenceIds = new Vector<String>();
			String ref;
			for (int i = begin; i < end; i++) {
				ref = references.get(i);
				ref = removeRefPrefix(ref); // remove mods NS prefixes, as this has not been done at getNewReferences
				if (!isValidXMLReference(ref)) {
					String xml2 = makeValidXMLReference(ref);
					if (xml2 != null) {
						subReferences.add(xml2);
					} else
						log(2, "Invalid Reference: "+ref);
				} else
					subReferences.add(ref);
			}
			// push references until none remain
			while (subReferences != null && !subReferences.isEmpty()) {
				log(1, "Push "+subReferences.size()+" NEW reference objects to project ["+_projectId+"] at repo ["+_repositoryId+"]");
				Map<Identifier, Identifier> idMap = Repository.ingestObjects(_repositoryId, _projectId, subReferences);
				if (!idMap.isEmpty()) {
					log(1, "Server returned ID map of length "+idMap.size());
					String newID;
					// XXX
					// XXX hier werden zwar die IDs und querverweise in allen objekten der lokalen DB
					// aktualisiert, allerdings nicht diejenigen in den objektkopien die in der liste 'references'
					// liegen. Deshalb kann es passieren (z.b. in issue 3487), dasz objekte mit querverweisen
					// auf lokale IDs hochgeladen werden sollen, die es lokal gar nicht mehr gibt und mit denen
					// der server sowieso nichts anfangen kann.
					// Evtl. kann man das problem dadurch beheben, dasz man einfach nicht stueckelt, sondern
					// alle objekte gleichzeitig zum server schickt. TODO Mal drueber nachdenken
					// XXX
					for (Identifier id : idMap.keySet()) {
						newID = idMap.get(id).toString();
						// look up global mapping for current id and append it to modifiedreferenceIds
						modifiedReferenceIds = checkModfiedIds(references, id, idMap, begin, modifiedReferenceIds);
						// rename object in all DB objects of type aodl, podl and mods
						resetObjectId(id, newID, 3);
					}
				}
				monitor.worked(subReferences.size());
	
				begin = end; // this seems about right
				end = (references.size() > NEWOBJECTS_PACKAGE_SIZE+end) ? (end+NEWOBJECTS_PACKAGE_SIZE) : references.size();  
				counter += subReferences.size();
				subReferences.clear();
	
				for (int i = begin; i < end; i++) {
					ref = references.get(i);
					ref = removeRefPrefix(ref); // remove mods prefixes now
					if (!isValidXMLReference(ref)) {
						String xml2 = makeValidXMLReference(ref);
						if (xml2 != null) {
							subReferences.add(xml2);
						} else
							log(2, "Invalid Reference: "+ref);
					} else
						subReferences.add(ref);
				}
			}
			// in local DB, move all Ids identified as having local changes from
			// the DB's 'modified' collection to persistent collections.
			if (modifiedReferenceIds != null && !modifiedReferenceIds.isEmpty()) 
				_idService.insertIdModifiedObject(modifiedReferenceIds, "pdrRo"); 
			// FIXME: ^ this doesn't seem to work out:
			// new objects are being send as modified objects even when they just have been ingested [3132, 4098, 3721] 
			log(0, "Done pushing NEW reference objects. Total number of pushed references: "+counter+"\n(out of "+references.size()+" new objects, server returned "+modifiedReferenceIds.size()+" global IDs)");
		}
	}

	/**
	 * Injest new persons.
	 * @param monitor the monitor
	 * @throws XQException the xQ exception
	 * @throws UnsupportedEncodingException the unsupported encoding exception
	 * @throws PDRAlliesClientException the pDR allies client exception
	 * @throws InvalidIdentifierException the invalid identifier exception
	 */
	private void injestNewPersons(final IProgressMonitor monitor) throws Exception
	{
		synchronized (_dbCon)
		{
			Vector<String> persons = new Vector<String>();
			for (String s : _mainSearcher.getNewPersons()) {
				s = removePersonPrefix(s); // podl prefix is removed from xml
				persons.add(s);
			}
			if (persons.size() == 0)
				return;
			log(1, "Begin ingest of "+persons.size()+" NEW person objects from local DB into remote repo");
			monitor.beginTask("Ingesting new Persons into Repository. Number of Objects: " + persons.size(),
					persons.size());

			int counter = 0;
			int begin = 0;
			int end = (persons.size() > NEWOBJECTS_PACKAGE_SIZE) ? NEWOBJECTS_PACKAGE_SIZE : persons.size();
			Vector<String> subPersons = new Vector<String>(end);
			Vector<String> modifiedPersonsIds = new Vector<String>();
			for (int i = begin; i < end; i++) {
				String xml = persons.get(i);
				if (!isValidXMLPerson(xml)) {
					String xml2 = makeValidXMLPerson(xml);
					if (xml2 != null) {
						subPersons.add(xml2);
					} else
						log(2, "Invalid New Person object: "+xml);
				} else
					subPersons.add(xml);
			}
			// push'n'chunk
			while (subPersons != null && !subPersons.isEmpty())	{
				log(1, "Push "+subPersons.size()+" NEW podl objects to project ["+_projectId+"] at repo ["+_repositoryId+"]");
				Map<Identifier, Identifier> idMap = Repository.ingestObjects(_repositoryId, _projectId, subPersons);

				if (!idMap.isEmpty()) {
					// System.out.println("size of map " + idMap.size());
					// XQConnection con = _dbCon.getConnection();
					// XQPreparedExpression xqp;
					// XQResultSequence xqs = null;
					// String replace;
					String newID;
					for (Identifier id : idMap.keySet()) {
						newID = idMap.get(id).toString();
						// find global ID provided by server for current id 
						modifiedPersonsIds = checkModfiedIds(persons, id, idMap, begin, modifiedPersonsIds);
						resetObjectId(id, newID, 2); // update all occurences of this id in local DB in aodl and podl objects
					}
				}
				monitor.worked(subPersons.size());
				begin = end; // seems legit
				end = (persons.size() > NEWOBJECTS_PACKAGE_SIZE + end) ? (end + NEWOBJECTS_PACKAGE_SIZE) : persons.size();
				counter += subPersons.size();
				subPersons.clear();

				for (int i = begin; i < end; i++) {
					String xml = persons.get(i);
					if (!isValidXMLPerson(xml)) {
						String xml2 = makeValidXMLPerson(xml);
						if (xml2 != null) {
							subPersons.add(xml2);
						} else
							log(2, "Invalid New Person object: "+xml);
					} else
						subPersons.add(xml);
				}
			}
			// set dirty status of all objects handled just now to 'clean'
			if (modifiedPersonsIds != null && !modifiedPersonsIds.isEmpty())
				_idService.insertIdModifiedObject(modifiedPersonsIds, "pdrPo");
			log(0, "Done pushing NEW podl objects. Total number of pushed persons: "+counter+"\n(out of "+persons.size()+" new objects, server returned "+modifiedPersonsIds.size()+" global IDs)");
		}
	}

	/**
	 * Injest new aspects.
	 * @param monitor the monitor
	 * @throws XQException the xQ exception
	 * @throws UnsupportedEncodingException the unsupported encoding exception
	 * @throws PDRAlliesClientException the pDR allies client exception
	 * @throws InvalidIdentifierException the invalid identifier exception
	 */
	private void injestNewAspects(final IProgressMonitor monitor) throws Exception
	{
		synchronized (_dbCon) {
			Vector<String> aspects = new Vector<String>();
			for (String s : _mainSearcher.getNewAspects()) {
				s = removeAspectPrefixes(s); // remove aodl prefix from xml
				aspects.add(s);
			}
			if (aspects.size() == 0)
				return;
			log(1, "Begin ingest of "+aspects.size()+" NEW aspect objects from local DB into remote repo");
			monitor.beginTask("Ingesting new Aspects into Repository. Number of Objects: " + aspects.size(),
					aspects.size());
	
			int counter = 0;
			int begin = 0;
			int end = (aspects.size() > NEWOBJECTS_PACKAGE_SIZE) ? NEWOBJECTS_PACKAGE_SIZE : aspects.size();
			Vector<String> subAspects = new Vector<String>(end);
			Vector<String> modifiedAspectIds = new Vector<String>();
			for (int i = begin; i < end; i++) {
				String xml = aspects.get(i);
				if (!isValidXMLAspect(xml)) {
					String xml2 = makeValidXMLAspect(xml);
					if (xml2 != null) {
						subAspects.add(xml);
					} else
						log(2, "Invalid aspect: "+xml);
				} else
					subAspects.add(xml);
			}
			// push'n'chunk until done
			while (subAspects != null && !subAspects.isEmpty()) {
				log(1, "Push "+subAspects.size()+" NEW aodl objects to project ["+_projectId+"] at repo ["+_repositoryId+"]");
				Map<Identifier, Identifier> idMap = Repository.ingestObjects(_repositoryId, _projectId, subAspects);
	
				if (!idMap.isEmpty()) {
					String newID;
					for (Identifier id : idMap.keySet()) {
						newID = idMap.get(id).toString();
						modifiedAspectIds = checkModfiedIds(aspects, id, idMap, begin, modifiedAspectIds);
						resetObjectId(id, newID, 1);
					}
				}
				monitor.worked(subAspects.size());
				begin = end; // ok
				end = (aspects.size() > NEWOBJECTS_PACKAGE_SIZE + end) ? (end + NEWOBJECTS_PACKAGE_SIZE) : aspects.size();
				counter += subAspects.size();
				subAspects.clear();
	
				for (int i = begin; i < end; i++) {
					String xml = aspects.get(i);
					if (!isValidXMLAspect(xml)) {
						String xml2 = makeValidXMLAspect(xml);
						if (xml2 != null) {
							subAspects.add(xml);
						} else
							log(2, "Invalid aspect: "+xml);
					} else
						subAspects.add(xml);
				}
			}
			//System.out.println("modifiedAspectIds size " + modifiedAspectIds.size());
			if (modifiedAspectIds != null && !modifiedAspectIds.isEmpty())
				_idService.insertIdModifiedObject(modifiedAspectIds, "pdrAo");
			log(0, "Done pushing NEW aodl objects. Total number of pushed aspects: "+counter+"\n(out of "+aspects.size()+" new objects, server returned "+modifiedAspectIds.size()+" global IDs)");
		}
	}

	/**
	 * Resolve object conflicts by one of the following strategies:
	 * <ul><li>Push and Force Overwrite of remote version with local changes</li>
	 * <li>Overwrite local changes with remote versions in local DB</li>
	 * <li>Do nothing, local object stays modified/new until prosponed conflict resolution is done at another time</li>
	 * </ul> 
	 * @param conObjects the con objects
	 * @param monitor the monitor
	 * @throws XMLStreamException the xML stream exception
	 * @throws UnsupportedEncodingException the unsupported encoding exception
	 * @throws PDRAlliesClientException the pDR allies client exception
	 * @throws XQException the xQ exception
	 */
	private void insertConflictingObjects(Vector<PDRObjectsConflict> conObjects, IProgressMonitor monitor)
			throws Exception {
		Vector<String> keepLocalObjects = new Vector<String>();

		String object = null;
		for (PDRObjectsConflict oc : conObjects) {
			// 1. conflicts that are resolved by keeping local version
			if (oc.isKeepLocal() && oc.getLocalObject() != null) {
				// for each conflict to be resolved by keeping the local version, 
				// test pdr type of local version, then write object XML,
				// remove NS prefixes, and add XML to list of local objects to be kept
				if (oc.getLocalObject() instanceof Aspect) {
					object = removeAspectPrefixes(_xmlProc.writeToXML(oc.getLocalObject()));
				} else if (oc.getLocalObject() instanceof Person) {
					object = removePersonPrefix(_xmlProc.writeToXML(oc.getLocalObject()));
				} else if (oc.getLocalObject() instanceof ReferenceMods)
					object = _xmlProc.writeToXML(oc.getLocalObject());
				// TODO: das kann man auch einfacher haben, wenn man dafuer sorgt, dasz alle typen entweder den NS dabei haben oder alle halt nicht
				// naja, jedenfalls wird lokales objekt fuer forced commit vorbereitet
				if (object != null)
					keepLocalObjects.add(object);
			} 
			// 2. conflicts that are resolved by deleting local version
			else if (oc.isOverrideLocal()) {
				// save remote version of object to local DB
				log(1, "Save remote version of object "+oc.getRepositoryObject().getDisplayNameWithID()+" to local DB");
				_dbManager.saveToDB(oc.getRepositoryObject(), false);
				monitor.worked(1);
			}
			// 3. conflicts to be prosponed are resolved later
			else if (oc.getLocalObject() != null) {// resolve conflict later, save id to be treated as modified.
				_idService.insertIdModifiedObject(oc.getLocalObject().getPdrId());
				// ID wird als modified gelistet, auszer sie ist neu. Auf jeden fall soll sie erstmal dirty bleiben
				log(1, "Prospone conflict resolution of object "+oc.getLocalObject().getPdrId());
			}
		}
		
		// Push local changes to repo for conflicts that have been selected for this handling 
		if (keepLocalObjects != null && !keepLocalObjects.isEmpty()) {
			log(1, "Overwrite "+keepLocalObjects.size()+" remote objects with local changes at Project "+_repositoryId+"/"+_projectId);
			Repository.modifyObjects(_repositoryId, _projectId, keepLocalObjects, true); // man beachte: force-flag!
			monitor.worked(keepLocalObjects.size());
		}
		log(0, "Handled "+conObjects.size()+" conflicts");
	}

	/**
	 * Proccess update states.
	 * @param idRanges the id ranges
	 * @param size the size
	 * @throws Exception
	 */
	private void proccessUpdateStates(final List<IDRange> idRanges, final int size) throws Exception
	{
		if (!idRanges.isEmpty())
		{
			Vector<String> ids;
			if (size > 0)
			{
				ids = new Vector<String>(size);
			}
			else
			{
				ids = new Vector<String>(20);
			}
			String type = null;
			HashMap<String, Integer> updateState = null;
			PdrId id;
			if (idRanges.get(0).getType() == PDRType.ASPECT)
			{
				type = "pdrAo";
				try
				{
					updateState = _facade.getAspectsUpdateState();
				}
				catch (Exception e)
				{
					log = new Status(IStatus.INFO, Activator.PLUGIN_ID, "Exception ", e);
					iLogger.log(log);				}
			}
			else if (idRanges.get(0).getType() == PDRType.PERSON)
			{
				type = "pdrPo";
				try
				{
					updateState = _facade.getPersonsUpdateState();
				}
				catch (Exception e)
				{
					log = new Status(IStatus.INFO, Activator.PLUGIN_ID, "Exception ", e);
					iLogger.log(log);
				}

			}
			else if (idRanges.get(0).getType() == PDRType.REFERENCE)
			{
				type = "pdrRo";
				try
				{
					updateState = _facade.getReferencesUpdateState();
				}
				catch (Exception e)
				{
					log = new Status(IStatus.INFO, Activator.PLUGIN_ID, "Exception ", e);
					iLogger.log(log);				}

			}
			// System.out.println(type);
			for (IDRange range : idRanges)
			{
				for (int i = range.getLowerBound(); i <= range.getUpperBound(); i++)
				{
					id = new PdrId(type, _repositoryId, _projectId, i);
					ids.add(id.toString());
					updateState.put(id.toString(), 1);
				}
			}
			_idService.insertIdUpdatedObjects(ids, type);
		}
	}

	/**
	 * Removes the aspect prefixes.
	 * @param s the s
	 * @return the string
	 */
	private String removeAspectPrefixes(String s)
	{
		Pattern openP = Pattern.compile("<aodl:");
		Pattern closeP = Pattern.compile("<\\/aodl:");
		Pattern nameP = Pattern.compile("xmlns:aodl");
		Pattern lb = Pattern.compile("\\r\\n");
		Pattern tab = Pattern.compile(">\\s{2,}<");

		Matcher m = openP.matcher(s);
		s = m.replaceAll("<");
		m = closeP.matcher(s);
		s = m.replaceAll("</");
		m = nameP.matcher(s);
		s = m.replaceAll("xmlns");
		// m = lb.matcher(s);
		// s = m.replaceAll("");
		m = tab.matcher(s);
		s = m.replaceAll("> <");
		// System.out.println("replaced aspect " + s);
		return s;
	}

	/**
	 * Removes podl namespace prefixes from person object XML serialization.
	 * @param personString the person string
	 * @return the string
	 */
	private String removePersonPrefix(String personString)
	{
		Pattern openP = Pattern.compile("<podl:");
		Pattern closeP = Pattern.compile("<\\/podl:");
		Pattern nameP = Pattern.compile("xmlns:podl");
		Pattern lb = Pattern.compile("\\r\\n");
		Pattern tab = Pattern.compile(">\\s+?<");

		Matcher m = openP.matcher(personString);
		personString = m.replaceAll("<");
		m = closeP.matcher(personString);
		personString = m.replaceAll("</");
		m = nameP.matcher(personString);
		personString = m.replaceAll("xmlns");

		// m = lb.matcher(personString);
		// personString = m.replaceAll("");

		m = tab.matcher(personString);
		personString = m.replaceAll("><");
		// System.out.println("replaced person " + personString);

		return personString;

	}

	/**
	 * Removes the ref prefix.
	 * @param s the s
	 * @return the string
	 */
	private String removeRefPrefix(String s)
	{
		Pattern openP = Pattern.compile("<mods:");
		Pattern closeP = Pattern.compile("<\\/mods:");
		Pattern nameP = Pattern.compile("xmlns:mods");
		Pattern lb = Pattern.compile("\\r\\n");
		Pattern tab = Pattern.compile(">\\s+?<");

		Matcher m = openP.matcher(s);
		s = m.replaceAll("<");
		m = closeP.matcher(s);
		s = m.replaceAll("</");
		m = nameP.matcher(s);
		s = m.replaceAll("xmlns");
		// m = lb.matcher(s);
		// s = m.replaceAll("");
		m = tab.matcher(s);
		s = m.replaceAll("><");

		// System.out.println("replaced ref " + s);
		return s;
	}

	/**
	 * Removes the user prefix.
	 * @param s the s
	 * @return the string
	 */
	private String removeUserPrefix(String s)
	{
		Pattern openP = Pattern.compile("<uodl:");
		Pattern closeP = Pattern.compile("<\\/uodl:");
		Pattern nameP = Pattern.compile("xmlns:uodl");
		Pattern tab = Pattern.compile(">\\s+?<");
		Pattern begin = Pattern.compile("<[?].*?[?]>");

		Matcher m = openP.matcher(s);
		s = m.replaceAll("<");
		m = closeP.matcher(s);
		s = m.replaceAll("</");
		m = nameP.matcher(s);
		s = m.replaceAll("xmlns");

		// m = lb.matcher(s);
		// s = m.replaceAll("");
		m = tab.matcher(s);
		s = m.replaceAll("><");
		m = begin.matcher(s);
		s = m.replaceAll("");
		// System.out.println("replaced user " + s);
		return s;
	}
	
	/**
	 * Removes the user prefix.
	 * @param s the s
	 * @return the string
	 */
	private String addUserPrefix(String s)
	{
		XMLReader xmlReader;
		try {
			xmlReader = new XMLFilterImpl(XMLReaderFactory.createXMLReader()) {
			    String namespace = "http://pdr.bbaw.de/namespaces/uodl/";
			    String pref = "uodl:";

			    @Override
			    public void startElement(String uri, String localName, String qName, Attributes atts)
			            throws SAXException {
			        super.startElement(namespace, localName, pref + qName, atts);
			    }

			    @Override
			    public void endElement(String uri, String localName, String qName) throws SAXException {
			        super.endElement(namespace, localName, pref + qName);
			    }
			};
			TransformerFactory tf = TransformerFactory.newInstance();
	        Transformer t;
	        StringWriter sw = new StringWriter();

			try {
				t = tf.newTransformer();
				t.transform(new SAXSource(xmlReader, new InputSource(new StringReader(s))), new StreamResult(sw));
				String str = sw.toString().substring(38);
				Pattern ns = Pattern.compile("xmlns=\"http://pdr.bbaw.de/namespaces/uodl/\"");

				Matcher m = ns.matcher(str);
				str = m.replaceAll("");
				
				return str;
			} catch (TransformerConfigurationException e) {
				log = new Status(IStatus.INFO, Activator.PLUGIN_ID, "Exception ", e);
				iLogger.log(log);
				return s;
			} catch (TransformerException e) {
				log = new Status(IStatus.INFO, Activator.PLUGIN_ID, "Exception ", e);
				iLogger.log(log);
				return s;
			}
		} catch (SAXException e1) {

			log = new Status(IStatus.INFO, Activator.PLUGIN_ID, "Exception ", e1);
			iLogger.log(log);
			}
		return s;
        
	}

	/**
	 * Retrieves object found under oldID, deletes it from DB and saves it
	 * under newId
	 * @param oldId the old id
	 * @param newID the new id
	 * @throws Exception
	 */
	private void renameObject(final Identifier oldId, final String newID) throws Exception
	{
		// FIXME: wenn man einfach das objekt das unter oldId liegt unter newId speichert, sind dann
		// nicht die ganzen IDs innerhalb des objektes total falsch?
		String xml;
		String col = null;
		if (oldId.getType().equals(PDRType.ASPECT))
			col = "aspect";
		if (oldId.getType().equals(PDRType.PERSON)) 
			col = "person";
		if (oldId.getType().equals(PDRType.REFERENCE))
			col = "reference";
		if (oldId.getType().equals(PDRType.USER))
			col = "users";

		if (col != null) {
			// get xml for object identified by old ID
			xml = _mainSearcher.getObjectXML(oldId.toString(), col);
			// System.out.println("renameobject xml " + xml);
			if (xml != null && xml.trim().length() > 0) {
				log(1, "Move object "+xml+"\nfrom old ID "+oldId+"\nto new ID "+newID);
				log = new Status(IStatus.INFO, Activator.PLUGIN_ID, "renameObject delete " + oldId.toString());
				//iLogger.log(log);
				_dbCon.delete(oldId.toString(), col);
				log = new Status(IStatus.INFO, Activator.PLUGIN_ID, "renameObject store newid " + newID.toString());
				//iLogger.log(log);
				// save object under new ID to DB
				_dbCon.store2DB(xml, col, newID.toString() + ".xml", true);
				log = new Status(IStatus.INFO, Activator.PLUGIN_ID, "renameObject renaming done " + newID.toString());
				//iLogger.log(log);
				//log(1, "Object under newID "+newID+":\n"+_mainSearcher.getObjectXML(newID, col));
			}

		}

	}


	
	private Status log(int level, String msg) {
		Status status = new Status(level, Activator.PLUGIN_ID, msg);
		iLogger.log(status);
		return status;
	}
	
	private Status log(int level, String msg, Throwable e) {
		if (e != null) {
			Status status = new Status(level, Activator.PLUGIN_ID, msg+"\n"+e.getMessage(), e);
			iLogger.log(status);
			return status;
		} else
			return log(level, msg);
	}
	

	@Override
	public final IStatus updateAllData(final String userID, final String password, final IProgressMonitor monitor)
			throws Exception {
		IStatus updateStatus = Status.OK_STATUS;
		Date currentUpdate;
		
		// TODO am besten komplette synchro nochmal von scratch neu schreiben
		
		// TODO wir muessen uns was ueberlegen falls keine user credentials zu haben sind. 
		// manchmal geht user wechseln ja schief und dann muessen wir nochmal login dialog oeffnen oder so 
		
		// TODO bei modified objects sicherstellen dasz zwei revisions drinstehen, die letzte mit aktuellem zeitstempel
		
		String url = Platform.getPreferencesService().getString(CommonActivator.PLUGIN_ID, "REPOSITORY_URL",
				AEConstants.REPOSITORY_URL, null);
		_repositoryId = Platform.getPreferencesService().getInt(CommonActivator.PLUGIN_ID, "REPOSITORY_ID",
				AEConstants.REPOSITORY_ID, null);
		_projectId = Platform.getPreferencesService().getInt(CommonActivator.PLUGIN_ID, "PROJECT_ID",
				AEConstants.PROJECT_ID, null);
		Configuration.getInstance().setAxis2BaseURL(url.toString());

		// check if remote is even a PDR server
		try {
			Repository.getTime();
		} catch (Exception e) {
			log(2, "Error: "+e.getMessage(), e);
			return new Status(IStatus.ERROR, Activator.PLUGIN_ID, e.getMessage());
		}
		
		Configuration.getInstance().setPDRUser(userID, password);
		log = new Status(IStatus.INFO, Activator.PLUGIN_ID, "url " + url.toString() + " userID " + userID + " p "
				+ "***");
		iLogger.log(log);
		boolean success = true;
		HashMap<String, Boolean> statuses = new HashMap<String, Boolean>(); 
		
		
		
		
		/////////////////////
		// injest new objects
		/////////////////////
		try	{
			////////
			// USERS
			////////
			// user ids aus DB collection pdrUo/new/id
			// user objekte von UserManager
			// XML serialisierung
			// XML parsing um projekt ID zu pruefen
			// XML parsing um standard user rauszufiltern
			// ingest von usern mit ID>9, update lokale DB
			// ingest standard user ohne DB update
			//log(IStatus.INFO, "Ingest of new Users", null);
			injestNewUsers(userID, password);
			//log(IStatus.OK, "New Users successfully ingested", null);
			statuses.put("ingest new users", true);
		} catch (PDRAlliesClientException e) {
			updateStatus = Status.CANCEL_STATUS;
			success = false;
			iLogger.log(new Status(IStatus.WARNING, Activator.PLUGIN_ID, "Exception at ALLIES library while ingesting new users: ", e));
			e.printStackTrace();
			statuses.put("ingest new users", false);
		} catch (Exception e) {
			success = false;
			log = new Status(IStatus.WARNING, Activator.PLUGIN_ID, "Exception while ingesting new users: ", e);
			iLogger.log(log);
			e.printStackTrace();
			statuses.put("ingest new users", false);
		}
		
		// new project, local user still does not yet exist in repository
/*		// XXX kann wahrscheinlich komplett weg, niemand sagt dasz das repo nen pdrAdmin mit dem pw hat (siehe musmig)
		if (!success) {
			//use pdrAdmin user to injest new users.
			log(IStatus.INFO, "New project; authenticate as pdrAdmin", null);
			// XXX ok
			//Configuration.getInstance().setPDRUser("pdrUo.001.002.000000001", "pdrrdp");
			Configuration.getInstance().setPDRUser("pdrUo.001.001.000000001", "pdrrdp");
			success = true;
			try {
				log(1, "Second attempt to ingest new user objects to repo", null);
				injestNewUsers(userID, password);
				log(0, "New users successfully ingested into repo", null);
				statuses.put("ingest new users", true);
			} catch (PDRAlliesClientException e) {
				updateStatus = Status.CANCEL_STATUS;
				success = false;
				log(IStatus.WARNING, "Exception in ALLIES while ingesting new users: ", e);
			} catch (Exception e) {
				success = false;
				log(2, "Exception while ingesting new users: ", e);
			}
			log(1, "Reset credentials for repo auth: "+userID+":"+password, null);
			Configuration.getInstance().setPDRUser(userID, password);

		}*/
		
		
		try {
			/////////////////
			// NEW LOCAL OBJS
			/////////////////
			// method returns id list of objects that are known to have failed to be ingested
			Vector<String> fails = ingestNewPDRObjects(monitor);
			if (fails != null && !fails.isEmpty()) {
				String logmsg = "At least "+fails.size()+" new local objects could not be ingested into remote:";
				for (String i : fails)
					logmsg+="\n"+i;
				log(2, logmsg);
				//..
				success = false;
			} else
				log(1, "Ingested new local objects without failures");
		} catch (PDRAlliesClientException e) {
			updateStatus = Status.CANCEL_STATUS;
			success = false;
			statuses.put("ingest new local objects", false);
			return log(2, "Exception in ALLIES while ingesting new local objects", e);
		} catch (Exception e) {
			success = false;
			log(IStatus.WARNING, "Exception while ingesting new local objects: ", e);
			statuses.put("ingest new local objects", false);
			return updateStatus;
		} 
		
		
		
		////////////////////
		// MODIFIED OBBJECTS
		////////////////////
		// XXX: local/repo version check
		
		// injest modified configs
		try {
			//////////
			// CONFIGS
			//////////
			// queries ID of modified configs from local DB
			// those identify category configuration providers, actually
			// their category configs are serialized into dtdl schema XML
			// they are uploaded to server with Utilities.setCategories method 
			log(1, "Begin to ingest modified configurations into repo");
			injestModifiedConfig(monitor);
			log(0, "Done ingesting modified configurations");
			statuses.put("update modified configs", true);
		} catch (PDRAlliesClientException e1) {
			success = false;
			updateStatus = log(2, "Exception during modified configurations ingest into repo: ", e1);
			statuses.put("update modified configs", false);
		} catch (Exception e1) {
			success = false;
			log(IStatus.WARNING, "Exception during ingest of modified configurations into repo: ", e1);
			statuses.put("update modified configs", false);
		}

		//////////////////////////
		// ingest modified objects
		//////////////////////////
		try	{
			/////////////////
			// MODIFIED USERS
			/////////////////
			// generate XMl for users known as modified by DB
			// send XML to server with overwrite flag set
			// don't mind update conflict list returned by server, as overwrite flag is set
			/////////////////
			//log(1, "Begin to ingest modified user objects into repo");
			injestModifiedUsers();
			//log(0, "Done ingesting modified users into repo");
			statuses.put("update modified users", true);
		} catch (PDRAlliesClientException e1) {
			success = false;
			updateStatus = log(2, "Exception during ingest of modified users", e1);
			statuses.put("update modified users", false);
		} catch (Exception e1) {
			success = false;
			log(2, "Exception during ingest of modified users", e1);
			statuses.put("update modified users", false);
		}

		
		try	{
			//////////////////////
			// MODIFIED REFERENCES
			//////////////////////
			// get XML from local DB
			// send to server and save returned conflict list
			//////////////////////
			//log(1, "Begin to ingest modified reference objects into repo");
			injestModifiedReferences(monitor);
			//log(0, "Done ingesting modified references");
			statuses.put("update modified mods", true);
		} catch (PDRAlliesClientException e1) {
			success = false;
			updateStatus = log(2, "Exception in ALLIES during ingest of modified references into repo: ", e1);
			statuses.put("update modified mods", false);
		} catch (Exception e1) {
			success = false;
			log(2, "Exception during ingest of modified references into repo: ", e1);
			statuses.put("update modified mods", false);
		}
		
		
		
		try {
			///////////////////
			// MODIFIED PERSONS
			///////////////////
			// get XMl from DB, remove ns prefixes
			// send to server, save update conflict list
			///////////////////
			//log(1, "Begin to ingest modified person objects into repo");
			injestModifiedPersons(monitor);
			//log(0, "Done ingesting modified person objects");
			statuses.put("update modified podl", true);
		} catch (PDRAlliesClientException e1) {
			success = false;
			updateStatus = log(2, "Exception in ALLIES during ingest of modified persons into repo: ", e1);
			statuses.put("update modified podl", false);
		} catch (Exception e1) {
			success = false;
			log(2, "Exception during ingest of modified persons into repo: ", e1);
			statuses.put("update modified podl", false);
		}

		
		
		try	{
			///////////////////
			// MODIFIED ASPECTS
			///////////////////
			// does the same as injestmodifiedpersons, but with aspects
			///////////////////
			//log(1, "Begin to ingest modified aspects into repo");
			injestModifiedAspects(monitor);
			//log(0, "Done ingesting modified aspects into repo");
			statuses.put("update modified aodl", true);
		} catch (PDRAlliesClientException e1) {
			success = false;
			updateStatus = log(2, "Exception in ALLIES during ingest of modified aspects into repo: ", e1);
			statuses.put("update modified aodl", false);
		} catch (Exception e1) {
			success = false;
			log(2, "Exception during ingest of modified aspects into repo: ", e1);
			statuses.put("update modified aodl", false);
		}
		
		
		////////////////////
		// CONFLICT HANDLING
		////////////////////
		// now we have three update conflict lists for the three object types for mods, podl, aodl
		//
		
		if ((_conflictingRepAspects != null && !_conflictingRepAspects.isEmpty())
				|| (_conflictingRepPersons != null && !_conflictingRepPersons.isEmpty())
				|| (_conflictingRepReferences != null && !_conflictingRepReferences.isEmpty()))
		{
			log(1, "Conflicts detected during ingest. Starting to resolve...");
			// all conflicts reported by server during update of modified objects
			// are being instantiated as PdrObjectsConflict with references
			// to PDRObject instances for both the local and the remote objects
			// remote object instance is being deserialized from XML returned by
			// server.
			// updateconflict dialog is openened, idservice is asked to clear update
			// states, then insertobjectconflict method is called 3x, at last facade
			// refreshes all its data
			handleObjectsConflicts(monitor);
		}
		// injest process completed. clear update states
		else if (success) {
			log(0, "Ingest of local changes successfully completed. No conflicts.");
			try	{
				//log(1, "Try to clear update states of local objects");
				_idService.clearAllUpdateStates();
				//log(0, "Update states cleared.");
				statuses.put("clear local object update states", true);
			} catch (XQException e1) {
				log(2, "Clearing update states of local objects failed: ", e1);
				statuses.put("clear local object update states", false);
			}
		}


		/////////////////////
		// GET REMOTE CHANGES
		/////////////////////
		//
		//
		/////////////////////
		
		// get all new or modified data

		// XXX neue oder modifizierte configs holen
		try	{
			getModifiedConfig(monitor);
			statuses.put("update remote configs modifications", true);
		} catch (PDRAlliesClientException e1) {
			updateStatus = Status.CANCEL_STATUS;
			success = false;
			log(2, "Failed to download modified classification configurations ", e1);
			statuses.put("update remote configs modifications", false);
		}

		// frage zeitpunkt des letzten updates aus lokaler datenbank ab
		// (default wert bei fehlern ist 1.1.2011)
		Date lastUpdateLocal = _idService.getUpdateTimeStamp();
		
		
		// push locally new [XXX], get ALL remote users and save them to local DB
		try	{
			////////
			// USERS
			////////
			updateUsers(userID, password, monitor); // TODO log attempt utilities getObjects
			statuses.put("update remote user modifications", true);
		} catch (Exception e) {
			log(2, "Synchronization of local and remote user obejcts failed: ", e);
			success = false;
			statuses.put("update remote user modifications", false);
		}

		if (monitor.isCanceled()) {
			success = false;
			return Status.CANCEL_STATUS;
		}
		
		// get remote repo clock
		try	{
			currentUpdate = AEConstants.ADMINDATE_FORMAT.parse(Repository.getTime());
		} catch (Exception e){
			// fallback: local time
			log(2, "Retrieval of remote repo's server time failed, use local time instead", e);
			currentUpdate = _facade.getCurrentDate();
		}
		
		// XXX ist es ein problem, hier schon den timestamp des laufenden updates zu bestimmen?
		log(1, "Local DB:\nSaved Timestamp of most recent repo update: "+AEConstants.ADMINDATE_FORMAT.format(lastUpdateLocal)+"\n"
				+"established timestamp of currently running update: " + AEConstants.ADMINDATE_FORMAT.format(currentUpdate));

		// wenn letztes update der lokalen instanz nach 2011 war, also glaubwuerdig ist:
		if (lastUpdateLocal.after(AEConstants.FIRST_EVER_UPDATE_TIMESTAMP)) {
			try	{
				// runterladen & speichern von objekten die auf remote seit lastUpdateLocal geaendert wurden
				updateModifiedObjects(monitor, lastUpdateLocal);
				statuses.put("update remote object modifications", true);
			} catch (PDRAlliesClientException e) {
				updateStatus = log(2, "Download of remote modified objects failed", e);
				statuses.put("update remote object modifications", false);
				success = false;
			} catch (Exception e) {
				success = false;
				log(2, "Download of remote modified objects failed", e);
				statuses.put("update remote object modifications", false);
			}
		} // wenn letztes update der lokalen instanz erstes update ueberhaupt war??? 
		else {
			try {
				/////////////////////////////////////////////////////////
				// einfach alle remote objekte rnuterladen und speichern?
				/////////////////////////////////////////////////////////
				updateAllOccupiedObjects(monitor); // TODO log attempt on utilities.getObjects
				statuses.put("clone remote objects", true);
			} catch (PDRAlliesClientException e) {
				updateStatus = Status.CANCEL_STATUS;
				success = false;
				log(2, "Download of remote repo failed ", e);
				statuses.put("clone remote objects", false);
			} catch (Exception e) {
				success = false;
				log(2, "Download of remote repo failed ", e);
				statuses.put("clone remote objects", false);
			}
		}
		
		// wenn alles gutgegangen ist, speicher zeitpunkt dieses updates
		if (success) {
			log(0, "***\nRepo update terminated successfully!\n***");
			try {
				// schreibe timestamp der laufenden synchro in DB
				_idService.setUpdateTimeStamp(currentUpdate);
			} catch (XQException e)	{
				log(2, "Updating local DB timestamp "+AEConstants.ADMINDATE_FORMAT.format(lastUpdateLocal)
						+" to "+AEConstants.ADMINDATE_FORMAT.format(currentUpdate)+" failed.", e);
			}
		} else {
			String msg = "ERRORS during repo update!\n";
			for (Entry<String, Boolean> st : statuses.entrySet())
				msg += st.getKey() + ": " + st.getValue() + "\n";
			log(2, msg);
		}
		log(1, "Timestamp of running update: "+ AEConstants.ADMINDATE_FORMAT.format(currentUpdate)
				+ "\nTimestamp of latest update as saved in local DB: "
				+AEConstants.ADMINDATE_FORMAT.format(_idService.getUpdateTimeStamp()));

		monitor.done();
		return updateStatus;

	}

	/**
	 * Download <b>all</b> aodl, podl and rodl objects from remote and save them to local DB.
	 * @param monitor the monitor
	 * @return the i status
	 * @throws Exception
	 */
	private IStatus updateAllOccupiedObjects(final IProgressMonitor monitor) throws Exception
	{
		String col = "util";
		String name;
		int totalWork = 0;
		int totalPersons = 0;
		int totalAspects = 0;
		int totalReferences = 0;
		List<IDRange> personRanges;
		List<IDRange> aspectRanges;
		List<IDRange> referenceRanges;

		personRanges = Utilities.getOccupiedObjectIDRanges(PDRType.PERSON, _repositoryId, _projectId, 1, MAX_OBJECT_NUMBER);
		aspectRanges = Utilities.getOccupiedObjectIDRanges(PDRType.ASPECT, _repositoryId, _projectId, 1, MAX_OBJECT_NUMBER);
		referenceRanges = Utilities.getOccupiedObjectIDRanges(PDRType.REFERENCE, _repositoryId, _projectId, 1, MAX_OBJECT_NUMBER);
		// calculate total work
		if (personRanges != null && !personRanges.isEmpty()) { 
			String logmsg="";
			for (IDRange range : personRanges) {
				logmsg += "\n"+range.getType().toString()+" ID range from "+range.getLowerBound()+" to "+range.getUpperBound();
				totalPersons = totalPersons + range.getUpperBound() - range.getLowerBound() + 1;
			}
			log(0, "Occupied global ID ranges for podl: "+logmsg);
		}
		if (aspectRanges != null && !aspectRanges.isEmpty()) {
			String logmsg="";
			for (IDRange range : aspectRanges)	{
				logmsg += "\n"+range.getType().toString()+" ID range from "+range.getLowerBound()+" to "+range.getUpperBound();
				totalAspects = totalAspects + range.getUpperBound() - range.getLowerBound() + 1;
			}
			log(0, "Occupied global ID ranges for aodl:"+logmsg);
		}
		if (referenceRanges != null && !referenceRanges.isEmpty()) {
			String logmsg="";
			for (IDRange range : referenceRanges) {
				logmsg+="\n"+range.getType().toString()+" ID range from "+range.getLowerBound()+" to "+range.getUpperBound();
				totalReferences = totalReferences + range.getUpperBound() - range.getLowerBound() + 1;
			}
			log(0, "Occupied global ID ranges for rodl mods: "+logmsg);
		}
		totalWork = totalPersons + totalAspects + totalReferences;
		monitor.beginTask("Updating from Repository. Number of Objects: " + totalWork, totalWork);
		if (monitor.isCanceled())
			return Status.CANCEL_STATUS;
		col = "person";
		int counter = 0;
		int lowerBound = 0;
		int upperBound = 0; // fixes issue #3949, where only person object in repo had id=1
		synchronized (_dbCon) {
			_dbCon.openCollection(col);
			String msg = "Remote confirmation of "+totalPersons+" person objects in "+personRanges.size()+" id ranges..";
			if (!personRanges.isEmpty()) try {
				for (IDRange range : personRanges) {
					msg += "\n persons range " + range.getLowerBound() + " upper bound " + range.getUpperBound()+"";
					lowerBound = range.getLowerBound();
	
					while (upperBound < range.getUpperBound()) {
						if (range.getUpperBound() - lowerBound <= PACKAGE_SIZE)	{
							upperBound = range.getUpperBound();
						}
						else
						{
							upperBound = lowerBound + PACKAGE_SIZE;
						}
						monitor.subTask("Updating " + totalPersons + " Persons from Repository... [Range " + lowerBound+"-"+upperBound+"]");
						Vector<String> objs = Utilities.getObjects(PDRType.PERSON, _repositoryId, _projectId, lowerBound,
								upperBound); //XXX allies auth error
						for (String s : objs)
						{
							name = extractPdrId(s) + ".xml";
							_dbCon.storeQuick2DB(s, col, name);
							s = null;
							monitor.worked(1);
						}
						counter += objs.size();
						lowerBound = Math.min(lowerBound + 250, range.getUpperBound()); // XXX wieso 250?
						if (monitor.isCanceled())
						{
							return Status.CANCEL_STATUS;
						}
					}
				}
			} catch (Exception e) {
				msg+="getObjects failed for person ID range "+lowerBound+"-"+upperBound+"\n";
				msg+=e.getMessage()+"\n";
				msg+=e.getStackTrace();
			}
			log(1, msg);
			_dbCon.closeDB(col);
		}
		if (monitor.isCanceled())
		{
			monitor.subTask("Optimizing Database Index");
			col = "person";
			_dbCon.optimize(col);
			try
			{
				proccessUpdateStates(personRanges, totalPersons);
			}
			catch (XQException e)
			{

				log = new Status(IStatus.INFO, Activator.PLUGIN_ID, "Exception ", e);iLogger.log(log);
			}
			monitor.done();
			return Status.CANCEL_STATUS;
		}
		String logmsg = "\nRemote person objects saved to local DB: "+counter+"/"+totalPersons;
		counter = 0;

		// aspect
		col = "aspect";
		lowerBound = 0;
		upperBound = 0;
		String msg = "Start downloading "+totalAspects+" aspect objects in "+aspectRanges.size()+" id ranges..";
		for (IDRange range : aspectRanges) {
			msg += "\n aspects range " + range.getLowerBound() + " upper bound " + range.getUpperBound()+"";
			lowerBound = range.getLowerBound();
			synchronized (_dbCon) // XXX warum wird hier bei jeder einzelnen range gelockt und nicht wie bei podl und mods ueber alle?
			{
				_dbCon.openCollection(col);
				while (upperBound < range.getUpperBound())
				{
					if (range.getUpperBound() - lowerBound <= PACKAGE_SIZE)
					{
						upperBound = range.getUpperBound();
					}
					else
					{
						upperBound = lowerBound + PACKAGE_SIZE;
					}
					monitor.subTask("Updating " + totalAspects + " Aspects from Repository... [Range "+lowerBound+"-" + upperBound+"]");

					Vector<String> objs = Utilities.getObjects(PDRType.ASPECT, _repositoryId, _projectId, lowerBound,
							upperBound);
					for (String s : objs)
					{
						// System.out.println(s);
						name = extractPdrId(s) + ".xml";
						_dbCon.storeQuick2DB(s, col, name);
						monitor.worked(1);

					}
					counter += objs.size();
					lowerBound = Math.min(lowerBound + 250, range.getUpperBound()); // XXX warum nicht package_size?
					if (monitor.isCanceled())
					{
						return Status.CANCEL_STATUS;
					}
				}
				log(1, msg);
				_dbCon.closeDB(col);

			}

		}
		if (monitor.isCanceled())
		{
			monitor.subTask("Optimizing Database Index");
			col = "person";
			_dbCon.optimize(col);
			col = "aspect";
			_dbCon.optimize(col);
			try
			{
				proccessUpdateStates(personRanges, totalPersons);
			}
			catch (XQException e)
			{

				log = new Status(IStatus.INFO, Activator.PLUGIN_ID, "Exception ", e);iLogger.log(log);
			}
			try
			{
				proccessUpdateStates(aspectRanges, totalAspects);
			}
			catch (XQException e)
			{

				log = new Status(IStatus.INFO, Activator.PLUGIN_ID, "Exception ", e);iLogger.log(log);
			}
			monitor.done();
			return Status.CANCEL_STATUS;
		}
		logmsg += "\nRemote aspect objects saved to local DB: "+counter+"/"+totalAspects;
		counter = 0;
		
		col = "reference";
		lowerBound = 1;
		upperBound = 1;
		synchronized (_dbCon)
		{
			msg = "Start downloading "+totalReferences+" reference objects in "+referenceRanges.size()+" id ranges..";
			_dbCon.openCollection(col);
			for (IDRange range : referenceRanges)
			{
				msg += "\n references range " + range.getLowerBound()+ " upper bound " + range.getUpperBound();
				lowerBound = range.getLowerBound();

				while (upperBound < range.getUpperBound())
				{
					if (range.getUpperBound() - lowerBound <= PACKAGE_SIZE)
					{
						upperBound = range.getUpperBound();
					}
					else
					{
						upperBound = lowerBound + PACKAGE_SIZE;
					}
					monitor.subTask("Updating " + totalReferences + " References from Repository... [Range " + lowerBound+"-"+upperBound+"]");
					Vector<String> objs = Utilities.getObjects(PDRType.REFERENCE, _repositoryId, _projectId,
							lowerBound, upperBound);
					for (String s : objs)
					{
						//System.out.println(s);
						//System.out.println();
						name = extractPdrId(s) + ".xml";
						_dbCon.storeQuick2DB(s, col, name);
						monitor.worked(1);
					}
					counter += objs.size();
					lowerBound = Math.min(lowerBound + 250, range.getUpperBound()); // XXX 250?? nicht package size? oder package size + 1?
					if (monitor.isCanceled())
					{
						return Status.CANCEL_STATUS;
					}
				}
			}
			log(1, msg);

			_dbCon.closeDB(col);
			if (monitor.isCanceled())
			{
				monitor.subTask("Optimizing Database Index");
				col = "person";
				_dbCon.optimize(col);
				col = "aspect";
				_dbCon.optimize(col);
				col = "reference";
				_dbCon.optimize(col);
				monitor.done();
				return Status.CANCEL_STATUS;
			}
			monitor.subTask("Optimizing Database Index");
			col = "person";
			_dbCon.optimize(col);
			col = "aspect";
			_dbCon.optimize(col);
			col = "reference";
			_dbCon.optimize(col);
			monitor.done();
			logmsg += "\nRemote reference objects saved to local DB: "+counter+"/"+totalReferences;
			log(1, logmsg);
			
			
			monitor.subTask("Processing Update State of Objects...");

			try
			{
				proccessUpdateStates(personRanges, totalPersons);
			}
			catch (XQException e)
			{

				log = new Status(IStatus.INFO, Activator.PLUGIN_ID, "Exception ", e);iLogger.log(log);
			}
			try
			{
				proccessUpdateStates(aspectRanges, totalAspects);
			}
			catch (XQException e)
			{

				log = new Status(IStatus.INFO, Activator.PLUGIN_ID, "Exception ", e);iLogger.log(log);
			}
			try
			{
				proccessUpdateStates(referenceRanges, totalReferences);
			}
			catch (XQException e)
			{

				log = new Status(IStatus.INFO, Activator.PLUGIN_ID, "Exception ", e);iLogger.log(log);
			}
		}
		return Status.OK_STATUS;

	}

	/**
	 * Download objects modified in remote repo and save to local DB, if not conflicting
	 * @param monitor the monitor
	 * @param date the date
	 * @return the i status
	 * @throws Exception
	 */
	private IStatus updateModifiedObjects(final IProgressMonitor monitor, final Date date) throws Exception
	{
		String col = "util";
		String name;
		monitor.subTask("Connecting to Repository...");
		log(1, "Query remote objects with modifications since "+AEConstants.ADMINDATE_FORMAT.format(date));
		List<String> modObjs = Repository.getModifiedObjects(_repositoryId, _projectId,
				AEConstants.ADMINDATE_FORMAT.format(date));
		// calculate total work

		monitor.beginTask("Updating from Repository. Number of Objects: " + modObjs.size(), modObjs.size());
		Vector<String> pIds = new Vector<String>(modObjs.size());
		Vector<String> rIds = new Vector<String>(modObjs.size());
		Vector<String> aIds = new Vector<String>(modObjs.size());
		Vector<String> uIds = new Vector<String>(modObjs.size());

		if (modObjs.size() < 0) {
			monitor.subTask("Your Database has already been updated. No Update necessary");
		} else	{
			log(1, "Retrieved "+modObjs.size()+" modified objects from remote. Begin to save to local DB..");
			monitor.subTask("Inserting Modified Objects into Local DB...");

			for (String s : modObjs) {
				// System.out.println(s);
				name = extractPdrId(s);
				if (name.startsWith("pdrPo")) {
					col = "person";
					pIds.add(name);
				}
				if (name.startsWith("pdrAo")) {
					col = "aspect";
					aIds.add(name);
				}
				if (name.startsWith("pdrRo")) {
					col = "reference";
					rIds.add(name); // TODO mods hat kein record/revision element, dafuer wird recordInfo genommen, aber nicht ausgewertet
					System.out.println("Mods object server sais was modified:\n"+s);
				}
				if (name.startsWith("pdrUo")) {
					col = "users";
					uIds.add(name);
				}
				// System.out.println("modified object " + s);
				name += ".xml";

				// XXX hier wird der fall nicht abgedeckt, in dem zwar die lokale version neuer ist als die auf remote,
				// die remote version jedoch ebenfalls neuer ist als das letzte lokale update. Ist das schlimm oder
				// wird das nachher beim conflict handling bemerkt?
				// XXX in mods gibt es doch ueberhaupt keine revision, wie soll man denn da feststellen welcehs objekt
				// neuer ist??? antwort: es wird stattdessen wohl recordInfo verwendet. Davon musz modl mindestens eines haben
				// allerdings wird das im SAXHandler nicht wirklich eingelesen
				if (!s.startsWith("no path in db registry") && checkVersions(s, col, name))
					synchronized (_dbCon) { 
						System.out.println("Save object modified on server to local DB: "+col+" "+name+" "+s);
						_dbCon.store2DB(s, col, name, false);
					}
			}
			monitor.worked(1);
		}

		monitor.subTask("Optimizing Database Index...");
		col = "person";
		_dbCon.optimize(col);
		col = "aspect";
		_dbCon.optimize(col);
		col = "reference";
		_dbCon.optimize(col);
		col = "users";
		_dbCon.optimize(col);
		monitor.subTask("Processing Update State of Objects...");

		for (String id : pIds) {
			try	{
				_facade.getPersonsUpdateState().put(id, 1);
			} catch (Exception e) {
				// TODO Auto-generated catch block
				log = new Status(IStatus.INFO, Activator.PLUGIN_ID, "Exception ", e);iLogger.log(log);
			}
		}
		_idService.insertIdUpdatedObjects(pIds, "pdrPo");
		for (String id : aIds) {
			try	{
				_facade.getAspectsUpdateState().put(id, 1);
			} catch (Exception e) {
				// TODO Auto-generated catch block
				log = new Status(IStatus.INFO, Activator.PLUGIN_ID, "Exception ", e);iLogger.log(log);
			}
		}
		_idService.insertIdUpdatedObjects(aIds, "pdrAo");
		for (String id : rIds) {
			try {
				_facade.getReferencesUpdateState().put(id, 1);
			} catch (Exception e) {
				// TODO Auto-generated catch block
				log = new Status(IStatus.INFO, Activator.PLUGIN_ID, "Exception ", e);iLogger.log(log);
			}
		}
		_idService.insertIdUpdatedObjects(rIds, "pdrRo");

		return Status.OK_STATUS;
	}

	@Override
	public final IStatus updateUsers(final String userID, final String password, final IProgressMonitor monitor)
			throws Exception {
		// XXX wieso hier extra nochmal anmelden? passiert in aufrufender methode schon
		String url = Platform.getPreferencesService().getString(CommonActivator.PLUGIN_ID, "REPOSITORY_URL",
				AEConstants.REPOSITORY_URL, null);
		_repositoryId = Platform.getPreferencesService().getInt(CommonActivator.PLUGIN_ID, "REPOSITORY_ID",
				AEConstants.REPOSITORY_ID, null);
		_projectId = Platform.getPreferencesService().getInt(CommonActivator.PLUGIN_ID, "PROJECT_ID",
				AEConstants.PROJECT_ID, null);
		String name;
		Configuration.getInstance().setAxis2BaseURL(url.toString());
		if (userID != null && password != null)	{
			Configuration.getInstance().setPDRUser(userID, password);
		} else {
			// anmelden als repository admin XXX warum projekt 2?
			Configuration.getInstance().setPDRUser("pdrUo." + String.format("%03d", _repositoryId) + ".001.000000001", "pdrrdp"); // XXX pdrAdmin funktioniert nicht auf musmig server
			//Configuration.getInstance().setPDRUser("pdrUo." + String.format("%03d", _repositoryId) + "." + String.format("%03d", _projectId) + ".000000001", "pdrrdp");
		}
		log(1, "Log in remote repo as: "+Configuration.getInstance().getPDRUserID());

		// push all users locally identified as NEW to remote repo
		injestNewUsers(userID, password); // XXX ist doch quatsch haben wir doch schon gemacht
		
		// retrieve remote repo user ID ranges 
		List<IDRange> ranges = Utilities.getOccupiedObjectIDRanges(PDRType.USER, _repositoryId, _projectId, 1, MAX_OBJECT_NUMBER);
		String col = "users";
		int lowerBound = 1; //XXX
		int upperBound = 1; //XXX
		synchronized (_dbCon) {
			_dbCon.openCollection(col);
			log(1, "Download remote repo user objects");
			for (IDRange range : ranges) {
				System.out.println("remote uodl ID range from " + range.getLowerBound() + " to " + range.getUpperBound());
				lowerBound = range.getLowerBound();

				while (upperBound < range.getUpperBound()) {
					if (range.getUpperBound() - lowerBound <= PACKAGE_SIZE)	{
						upperBound = range.getUpperBound();
					} else
						upperBound = lowerBound + PACKAGE_SIZE;

					// retrieve remote user objects
					//try {
					System.out.println("Download user objects in range");
					Vector<String> objs = Utilities.getObjects(PDRType.USER, _repositoryId, _projectId, lowerBound, // XXX auth error as pdrAdmin. handle!
							upperBound);
					for (String s : objs) {
						name = extractPdrId(s) + ".xml";
						if (isValidUser(s))	{
							_dbCon.storeQuick2DB(addUserPrefix(s), col, name); // XXX warum uodl prefixes reinschrauben?
						} else {
							String us = addUserPrefix(s);
							if (isValidUser(us))
								_dbCon.storeQuick2DB(us, col, name); // XXX was macht die methode?
						}
					}
					System.out.println("Stored "+objs.size()+" user objects from repo to local DB");
					/*} catch (Exception e) {
						log(2, "Updating user objects from remote failed: ", e);
					}*/
					lowerBound = Math.min(lowerBound + PACKAGE_SIZE, range.getUpperBound());
				}
			}
			_dbCon.optimize(col);
			_dbCon.openCollection(col);
			_dbCon.closeDB(col);
			_idService.clearUserUpdateStates();
			Configuration.getInstance().setPDRUser(userID, password); // XXX never called cause of pdrAdmin auth error above
			log(1, "Logging into remote repo as "+Configuration.getInstance().getPDRUserID());
		}
		return null;
	}

	private boolean isValidUser(String s)
	{
		if (s.startsWith("<user xmlns=\"http://pdr.bbaw.de/namespaces/uodl/\" xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\""))
		{
			return true;
		}
		else if (s
				.startsWith("<uodl:user xmlns:uodl=\"http://pdr.bbaw.de/namespaces/uodl/\" xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\""))
		{
			return true;
		}
		else
		{
			return false;
		}
	}

	/**
	 * Move local DB object stored under id to newID, then update
	 * all references to this object found in the DB according to level parameter.
	 * (level = 4: update all objects up to uodl, 3: up to mods, 2: up to podl, 1: only aodl)
	 * @param id
	 * @param newID
	 * @param level
	 * @throws Exception
	 */
	private void resetObjectId(Identifier id, String newID, int level) throws Exception {
		XQConnection con;
		con = _dbCon.getConnection();
		XQPreparedExpression xqp;
		XQResultSequence xqs = null;
		String replace;
		log = new Status(IStatus.INFO, Activator.PLUGIN_ID, "resetObjectId old: " + id.toString() + " new: " + newID);
		iLogger.log(log);
		boolean successful = false;
		try	{
			renameObject(id, newID); // moves object from id to newId in local DB
			successful = true;
		} catch (XQException e2) {
			log(2, "Could not move object from "+id+" to "+newID, e2);
		}

		if (successful)	{
			//log(1, "Object under newID "+newID+":\n"+_mainSearcher.getObjectXML(newID, col));
			// update all ID references in DB user objects
			if (level >= 4)	{ 
				replace = "declare namespace uodl=\"http://pdr.bbaw.de/namespaces/uodl/\";\n"
						+ "for $x in collection(\"users\")/uodl:user//@*[.='" + id.toString() + "']\n"
						+ "let $new := '" + newID + "'\n" + "return replace value of node $x with $new";
				try	{
					con = _dbCon.getConnection();
					xqp = con.prepareExpression(replace);
					xqs = xqp.executeQuery();
					xqs.close();
					con.close();
				} catch (XQException e) 	{
					log(2, "Could not update user object references to "+id, e);
				}
				// _dbCon.optimize("users");
			}

			// update all ID reference in DB reference objects
			if (level >= 3) 	{
				replace = "declare namespace mods=\"http://www.loc.gov/mods/v3\";\n"
						+ "for $x in collection(\"reference\")/mods:mods//@*[.='" + id.toString() + "']\n"
						+ "let $new := '" + newID + "'\n" + "return replace value of node $x with $new";
				//System.out.println(replace);
				try	{
					con = _dbCon.getConnection();
					xqp = null;
					xqp = con.prepareExpression(replace);
					xqs = xqp.executeQuery();
					xqs.close();
					con.close();
				} catch (XQException e)	{
					log(2, "Could not update mods object references to "+id, e);
				}

				// replace = "for $x in collection(\"reference\")/mods//*[.='" +
				// id.toString() + "']\n" +
				// "let $new := '" + idMap.get(id).toString() + "'\n" +
				// "return replace value of node $x with $new";
				// System.out.println(replace);
				// xqp = con.prepareExpression(replace);
				// xqs = xqp.executeQuery();
				// _dbCon.optimize("reference");

			}

			// update all ID references in DB person objects
			if (level >= 2) {
				replace = "declare namespace podl=\"http://pdr.bbaw.de/namespaces/podl/\";\n"
						+ "for $x in collection(\"person\")/podl:person//@*[.='" + id.toString() + "']\n"
						+ "let $new := '" + newID + "'\n" + "return replace value of node $x with $new";
				//System.out.println(replace);
				try {
					con = _dbCon.getConnection();
					xqp = null;
					xqp = con.prepareExpression(replace);
					xqs = xqp.executeQuery();
					xqs.close();
					con.close();
				} catch (XQException e) {
					log(2, "Could not update person object references to "+id, e);
				}

				replace = "declare namespace podl=\"http://pdr.bbaw.de/namespaces/podl/\";\n"
						+ "for $x in collection(\"person\")/podl:person//podl:reference[.='" + id.toString() + "']\n"
						+ "let $new := '" + newID + "'\n" + "return replace value of node $x with $new";
				//System.out.println(replace);
				try	{
					con = _dbCon.getConnection();
					xqp = null;
					xqp = con.prepareExpression(replace);
					xqs = xqp.executeQuery();
					xqs.close();
					con.close();
				} catch (XQException e1) {
					log(2, "Could not update person object (reference element) references to "+id, e1);
				}
				// _dbCon.optimize("person");

			}

			// update ID references in attributes in local aspects objects
			if (level >= 1)	{
				replace = "declare namespace aodl=\"http://pdr.bbaw.de/namespaces/aodl/\";\n"
						+ "for $x in collection(\"aspect\")/aodl:aspect//@*[.='" + id.toString() + "']\n"
						+ "let $new := '" + newID + "'\n" + "return replace value of node $x with $new";
				//System.out.println(replace);
				try	{
					con = _dbCon.getConnection();
					xqp = null;
					xqp = con.prepareExpression(replace);
					xqs = xqp.executeQuery();
					xqs.close();
					con.close();
				} catch (XQException e)	{
					log(2, "Could not update aspect object references to "+id, e);
				}

				replace = "declare namespace aodl=\"http://pdr.bbaw.de/namespaces/aodl/\";\n"
						+ "for $x in collection(\"aspect\")/aodl:aspect//aodl:reference[.='" + id.toString() + "']\n"
						+ "let $new := '" + newID + "'\n" + "return replace value of node $x with $new";
				//System.out.println(replace);
				try	{
					con = _dbCon.getConnection();
					xqp = null;
					xqp = con.prepareExpression(replace);
					xqs = xqp.executeQuery();
					xqs.close();
					con.close();
				} catch (XQException e)	{
					log(2, "Could not update aspect object (reference element) references to "+id, e);
				}
				// _dbCon.optimize("aspect");

			}

		}

	}

	private void checkAndInjestStandardUsers(Vector<String> standardUsers, String userId, String password)
	{
		log(1, "Prepare to check and possibly ingest standard users");
		Collections.sort(standardUsers);
		Vector<String> repoUsers = new Vector<String>(10);
		// XXX wieso immer projekt nr 2?
		// XXX kann man sich nicht drauf verlassen dasz es immer nen pdrAdmin mit dem pw gibt.
		if (userId != null && password != null) {
			Configuration.getInstance().setPDRUser(userId, password);
		} else
			Configuration.getInstance().setPDRUser("pdrUo." + String.format("%03d", _repositoryId) + ".001.000000001", "pdrrdp"); // works
		//Configuration.getInstance().setPDRUser("pdrUo." + String.format("%03d", _repositoryId) + ".002.000000001", "pdrrdp");
		//Configuration.getInstance().setPDRUser("pdrUo." + String.format("%03d", _repositoryId) + "." + String.format("%03d", _projectId) + ".000000001", "pdrrdp");
		log(1, "Logging into remote as "+Configuration.getInstance().getPDRUserID());
		try	{
			repoUsers = Utilities.getObjects(PDRType.USER, _repositoryId, _projectId, 1, 9);
		} catch (PDRAlliesClientException e2) {
			log(2, "Download of remote repo user definitions failed,\npossibly due to failed authentication as "+Configuration.getInstance().getPDRUserID(), e2);
			// XXX exception should be thrown
		}
		Collections.sort(repoUsers);
		boolean found = false;
		for (int i = 1; i < 10; i++) {
			String user = standardUsers.get(i - 1);
			if (user != null && new Integer(extractPdrId(user).substring(14)) <= 9) {
				found = false;
				for (String u : repoUsers)
					if (extractPdrId(u).equals(extractPdrId(user)))
						found = true; // standarduser is already present on remote, yay!
				if (!found) {
					Vector<String> injestUsers = new Vector<String>(1);
					User newUser = null;
					if (new Integer(extractPdrId(user).substring(14)) == 1) {
						newUser = _userManager.createUser(new PdrId("pdrUo", _repositoryId, _projectId, 100000001),
								"pdrAdmin", "pdrrdp", new String[]
								{"pdrAdmin", "admin", "user"}, "pdrAdmin", "pdrAdmin", "PDR-Administrator");
					} else if (new Integer(extractPdrId(user).substring(14)) == 2) {
						newUser = _userManager.createUser(new PdrId("pdrUo", _repositoryId, _projectId, 100000002),
								"admin", "admin", new String[]
								{"admin", "user"}, "admin", "admin", "Project-Administrator");
					} else if (new Integer(extractPdrId(user).substring(14)) == 3) {
						newUser = _userManager.createUser(new PdrId("pdrUo", _repositoryId, _projectId, 100000003),
								"user", "user", new String[]
								{"user"}, "user", "user", "Project-User");
					} else if (new Integer(extractPdrId(user).substring(14)) == 4) {
						newUser = _userManager.createUser(new PdrId("pdrUo", _repositoryId, _projectId, 100000004),
								"guest", "guest", new String[]
								{"guest"}, "guest", "guest", "Project-Guest");
					} else if (new Integer(extractPdrId(user).substring(14)) == 5) {
						newUser = _userManager.createUser(new PdrId("pdrUo", _repositoryId, _projectId, 100000005),
								"computer", "computer", new String[]
								{"user"}, "computer", "computer", "computer");
					} else if (new Integer(extractPdrId(user).substring(14)) == 6) {
						newUser = _userManager.createUser(new PdrId("pdrUo", _repositoryId, _projectId, 100000006),
								"dummy", "dummy", new String[]
								{"dummy"}, "dummy", "dummy", "dummy");
					} else if (new Integer(extractPdrId(user).substring(14)) == 7) {
						newUser = _userManager.createUser(new PdrId("pdrUo", _repositoryId, _projectId, 100000007),
								"dummy", "dummy", new String[]
								{"dummy"}, "dummy", "dummy", "dummy");
					} else if (new Integer(extractPdrId(user).substring(14)) == 8) {
						newUser = _userManager.createUser(new PdrId("pdrUo", _repositoryId, _projectId, 100000008),
								"dummy", "dummy", new String[]
								{"dummy"}, "dummy", "dummy", "dummy");
					} else if (new Integer(extractPdrId(user).substring(14)) == 9) {
						newUser = _userManager.createUser(new PdrId("pdrUo", _repositoryId, _projectId, 100000009),
								"dummy", "dummy", new String[]
								{"dummy"}, "dummy", "dummy", "dummy");
					}
					
					try	{
						user = new UserXMLProcessor().writeToXML(newUser);
					} catch (XMLStreamException e1)	{
						// TODO Auto-generated catch block
						log = new Status(IStatus.INFO, Activator.PLUGIN_ID, "Exception ", e1);iLogger.log(log);
					}
					
					// XXX einzeln ingesten? echt???
					injestUsers.add(removeUserPrefix(user));
					log(1, "Ingest "+injestUsers.size()+" standard users to remote");
					try	{
						// XXX persistente IDs werden nicht verarbeitet??? rueckgabe wird infach weggeschmissen?
						// wohl weils standard user sind
						//Repository.ingestObjects(_repositoryId, _projectId, injestUsers);
						Map<Identifier, Identifier> idMap = Repository.ingestObjects(_repositoryId, _projectId, injestUsers);
						for (Entry<Identifier, Identifier> mapping : idMap.entrySet())
							System.out.println(" "+mapping.getKey()+" -> "+mapping.getValue());
					} catch (InvalidIdentifierException e) {
						log = new Status(2, Activator.PLUGIN_ID, "Invalid ID during ingest of standard user[s] "+injestUsers, e);iLogger.log(log);
					} catch (PDRAlliesClientException e) {
						log = new Status(2, Activator.PLUGIN_ID, "Allies Error during ingest of standard user[s] "+injestUsers
								+"\nAuthentification seems to have failed for "+Configuration.getInstance().getPDRUserID(), e);iLogger.log(log);
					}
				} else
					log(1, "Standard user "+extractPdrId(user)+" already present on remote repo");
			}
		}
		// reset repo authentification to locally logged in user creds
		Configuration.getInstance().setPDRUser(userId, password);
		log(1, "Logging into remote repo as "+Configuration.getInstance().getPDRUserID());
	}

	@Override
	public String getUserId(String userName, int projectID) throws PDRAlliesClientException
	{
		String url = Platform.getPreferencesService().getString(CommonActivator.PLUGIN_ID, "REPOSITORY_URL",
				AEConstants.REPOSITORY_URL, null);
		Configuration.getInstance().setAxis2BaseURL(url.toString());
		log(1, "Request ID lookup for user "+userName+" in project "+projectID+" at remote repo "+url);
		String id = Repository.getUserID(userName, projectID);
		log(1, "Remote responds with ID "+id);
		return id;
	}

	@Override
	public void loadInitialUsers(String userID, String password,
			IProgressMonitor monitor) throws Exception {
		String url = Platform.getPreferencesService().getString(CommonActivator.PLUGIN_ID, "REPOSITORY_URL",
				AEConstants.REPOSITORY_URL, null);
		_repositoryId = Platform.getPreferencesService().getInt(CommonActivator.PLUGIN_ID, "REPOSITORY_ID",
				AEConstants.REPOSITORY_ID, null);
		_projectId = Platform.getPreferencesService().getInt(CommonActivator.PLUGIN_ID, "PROJECT_ID",
				AEConstants.PROJECT_ID, null);
		String name;
		Configuration.getInstance().setAxis2BaseURL(url.toString());
		// 
		if (userID != null && password != null)	{
			Configuration.getInstance().setPDRUser(userID, password);
		} else {
			// fallback to pdrAdmin
			// project ID not relevant in fallback user id? no. pdrAdmin exists only in project 001
			//Configuration.getInstance().setPDRUser("pdrUo." + String.format("%03d", _repositoryId) + "."+String.format("%03d",_projectId)+".000000001", "pdrrdp");
			Configuration.getInstance().setPDRUser("pdrUo." + String.format("%03d", _repositoryId) + ".001.000000001", "pdrrdp");
		}

		
		List<IDRange> ranges = Utilities.getOccupiedObjectIDRanges(PDRType.USER, _repositoryId, _projectId, 1,
				MAX_OBJECT_NUMBER);
		String col = "users";
		int lowerBound = 0;
		int upperBound = 0;
		synchronized (_dbCon)
		{
			_dbCon.openCollection(col);
			for (IDRange range : ranges)
			{
				log = new Status(IStatus.INFO, Activator.PLUGIN_ID, "user range " + range.getLowerBound() + " upper b "
						+ range.getUpperBound());
				iLogger.log(log);
				lowerBound = range.getLowerBound();

				while (upperBound < range.getUpperBound())
				{
					if (range.getUpperBound() - lowerBound <= PACKAGE_SIZE)
					{
						upperBound = range.getUpperBound();
					}
					else
					{
						upperBound = lowerBound + PACKAGE_SIZE;
					}

					Vector<String> objs = Utilities.getObjects(PDRType.USER, _repositoryId, _projectId, lowerBound,
							upperBound);
					for (String s : objs)
					{
						name = extractPdrId(s) + ".xml";
						log = new Status(IStatus.INFO, Activator.PLUGIN_ID, "update user  " + name );
						iLogger.log(log);
						if (isValidUser(s))
						{
							_dbCon.delete(name, col);
							_dbCon.store2DB(addUserPrefix(s), col, name, false);
						}
						else
						{
							String us = addUserPrefix(s);
							if (isValidUser(us))
							{
								_dbCon.delete(name, col);
								_dbCon.store2DB(us, col, name, false);
							}
						}
					}
					lowerBound = Math.min(lowerBound + PACKAGE_SIZE, range.getUpperBound());
				}
			}
			_dbCon.optimize(col);
			_dbCon.openCollection(col);
			_dbCon.closeDB(col);
			_idService.clearUserUpdateStates();
			Configuration.getInstance().setPDRUser(userID, password);

		}
		
	}

}
