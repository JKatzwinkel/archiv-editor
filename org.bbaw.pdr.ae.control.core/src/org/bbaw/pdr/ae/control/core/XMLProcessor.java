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
package org.bbaw.pdr.ae.control.core;

import java.io.ByteArrayOutputStream;
import java.io.UnsupportedEncodingException;
import java.text.SimpleDateFormat;
import java.util.HashMap;
import java.util.Vector;

import javax.xml.stream.XMLEventFactory;
import javax.xml.stream.XMLEventWriter;
import javax.xml.stream.XMLOutputFactory;
import javax.xml.stream.XMLStreamException;
import javax.xml.stream.events.Characters;
import javax.xml.stream.events.EndElement;
import javax.xml.stream.events.StartDocument;
import javax.xml.stream.events.StartElement;
import javax.xml.stream.events.XMLEvent;

import org.bbaw.pdr.ae.common.AEConstants;
import org.bbaw.pdr.ae.control.internal.Activator;
import org.bbaw.pdr.ae.metamodel.PdrMetaObject;
import org.bbaw.pdr.ae.metamodel.Record;
import org.bbaw.pdr.ae.metamodel.Revision;
import org.bbaw.pdr.ae.model.Aspect;
import org.bbaw.pdr.ae.model.Concurrence;
import org.bbaw.pdr.ae.model.Identifier;
import org.bbaw.pdr.ae.model.NameMods;
import org.bbaw.pdr.ae.model.OriginInfo;
import org.bbaw.pdr.ae.model.PartMods;
import org.bbaw.pdr.ae.model.PdrObject;
import org.bbaw.pdr.ae.model.Person;
import org.bbaw.pdr.ae.model.Place;
import org.bbaw.pdr.ae.model.Reference;
import org.bbaw.pdr.ae.model.ReferenceMods;
import org.bbaw.pdr.ae.model.ReferenceModsTemplate;
import org.bbaw.pdr.ae.model.RelatedItem;
import org.bbaw.pdr.ae.model.Relation;
import org.bbaw.pdr.ae.model.RelationStm;
import org.bbaw.pdr.ae.model.SemanticStm;
import org.bbaw.pdr.ae.model.SpatialDim;
import org.bbaw.pdr.ae.model.SpatialStm;
import org.bbaw.pdr.ae.model.TaggingRange;
import org.bbaw.pdr.ae.model.TimeDim;
import org.bbaw.pdr.ae.model.TimeStm;
import org.bbaw.pdr.ae.model.ValidationStm;
import org.eclipse.core.runtime.ILog;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;

/**
 * The Class XMLProcessor.
 * @author Christoph Plutte
 */
public class XMLProcessor implements XMLProcessorInterface
{

	/** The _admin date format. */
	private SimpleDateFormat _adminDateFormat = AEConstants.ADMINDATE_FORMAT;

	/** The _encoding. */
	private final String _encoding = "iso8601";

	/** The _mods uri. */
	private final String _modsUri = "http://www.loc.gov/mods/v3";

	/** Logger. */
	private static ILog iLogger = AEConstants.ILOGGER;

	private String logmsg = "";
	
	private void buflog(String line) {
		logmsg += line + "\n";
	}
	
	private void log(int level, String msg, Exception e) {
		iLogger.log(new Status(level, Activator.PLUGIN_ID, msg, e));
	}
	
	
	/**
	 * Creates {@link Concurrence} node.
	 * @param eventWriter the event writer
	 * @param name the name of node
	 * @param c the concurrence
	 * @param person 
	 * @throws XMLStreamException the xML stream exception
	 */
	private void createPersonConcurrenceNode(final XMLEventWriter eventWriter, final String name, final Concurrence c, PdrMetaObject person)
			throws XMLStreamException
	{
		XMLEventFactory eventFactory = XMLEventFactory.newInstance();

		// Create Start node
		StartElement sElement = eventFactory.createStartElement("podl", "http://pdr.bbaw.de/namespaces/podl/", name);

		eventWriter.add(sElement);
		// FIXME nullpointer abfangen!!1
		eventWriter.add(eventFactory.createAttribute("person", c.getPersonId().toString()));


		if (c.getReferences() != null)
		{
			for (int j = 0; j < c.getReferences().size(); j++)
			{
				createValidationStmNode(eventWriter, "validationStm", c.getReferences().get(j), "podl",
						"http://pdr.bbaw.de/namespaces/podl/", person);
			}
		}
		// Create End node
		EndElement eElement = eventFactory.createEndElement("podl", "http://pdr.bbaw.de/namespaces/podl/", name);
		eventWriter.add(eElement);


	}

	/**
	 * Creates the node.
	 * @param eventWriter the event writer
	 * @param name the name
	 * @param d the documentation
	 * @throws XMLStreamException the xML stream exception
	 */
	private void createModsTemplateDocumentationNode(final XMLEventWriter eventWriter, final String name, final HashMap<String, String> d)
			throws XMLStreamException
	{

		XMLEventFactory eventFactory = XMLEventFactory.newInstance();
		// Create Start node
		StartElement sElement = eventFactory.createStartElement("", "", name);

		eventWriter.add(sElement);
		// FIXME nullpointer abfangen!!1


		for (String str : d.keySet())
		{

			createModsTemplateDocPartNode(eventWriter, "docPart", d.get(str), str);
		}
		if (d.isEmpty())
		{
			createModsTemplateDocPartNode(eventWriter, "docPart", "", "de");

		}
		eventWriter.add(eventFactory.createEndElement("", "", name));


	}

	// private void createNode(XMLEventWriter eventWriter, String name,
	// Reference ref, String prefix, String uri) throws XMLStreamException {
	// XMLEventFactory eventFactory = XMLEventFactory.newInstance();
	// XMLEvent end = eventFactory.createCharacters("\n");
	//
	// // Create Start node
	// StartElement sElement = eventFactory.createStartElement(prefix, uri,
	// name);
	//
	// eventWriter.add(sElement);
	// if (ref.getInternal() != null)
	// eventWriter.add(eventFactory.createAttribute("internal",
	// ref.getInternal()));
	// if (ref.getQuality() !=
	// null)eventWriter.add(eventFactory.createAttribute("quality",
	// ref.getQuality()));
	// if (ref.getAuthority() !=
	// null)eventWriter.add(eventFactory.createAttribute("authority",
	// ref.getAuthority().toString()));
	//
	// // Create Content
	// if (ref.getSourceId() != null)
	// {
	// Characters characters =
	// eventFactory.createCharacters(ref.getSourceId().toString());
	// eventWriter.add(characters);
	// }
	// // Create End node
	// EndElement eElement = eventFactory.createEndElement(prefix, uri, name);
	// eventWriter.add(eElement);
	//
	// }

	/**
	 * Creates Identifier node.
	 * @param eventWriter the event writer
	 * @param name the name
	 * @param i the identifier
	 * @throws XMLStreamException the xML stream exception
	 */
	private Vector<XMLEvent> createPersonIdentifierNodes(final XMLEventWriter eventWriter, final String name, final Identifier i)
			throws XMLStreamException
	{
		Vector<XMLEvent> idXmlEvs = new Vector<XMLEvent>();
		XMLEventFactory eventFactory = XMLEventFactory.newInstance();
		// Create Start node
		StartElement sElement = eventFactory.createStartElement("podl", "http://pdr.bbaw.de/namespaces/podl/", name);
		idXmlEvs.add(sElement);
		// attr provider is required
		if (i.getProvider() == null) {
			buflog("Podl warning: identifier without provider attribute");
			return null;
		} else 
			idXmlEvs.add(eventFactory.createAttribute("provider", i.getProvider()));
		
		if (i.getQuality() == null) {
			buflog("Podl warning: identifier without quality attribute");
			return null;
		} else		
			idXmlEvs.add(eventFactory.createAttribute("quality", i.getQuality()));
		
		if (i.getAuthority() == null) {
			buflog("Podl warning: identifier without authority attribute");
			return null;
		} else
			idXmlEvs.add(eventFactory.createAttribute("authority", i.getAuthority().toString()));
		
		// Create Content
		Characters characters = eventFactory.createCharacters(i.getIdentifier());
		idXmlEvs.add(characters);
		// Create End node
		EndElement eElement = eventFactory.createEndElement("podl", "http://pdr.bbaw.de/namespaces/podl/", name);
		idXmlEvs.add(eElement);
		
		return idXmlEvs;


	}

	/**
	 * Creates the node.
	 * @param eventWriter the event writer
	 * @param name the name
	 * @param nameMods the namemods object
	 * @param prefix the prefix
	 * @param uri the uri
	 * @throws XMLStreamException the xML stream exception
	 */
	private void createModsNameNode(final XMLEventWriter eventWriter, final String name, final NameMods nameMods,
			final String prefix, final String uri) throws XMLStreamException
	{
		XMLEventFactory eventFactory = XMLEventFactory.newInstance();
		// Create Start node
		StartElement sElement = eventFactory.createStartElement(prefix, uri, "name");
		eventWriter.add(sElement);
		if (nameMods.getType() != null)
		{
			eventWriter.add(eventFactory.createAttribute("type", nameMods.getType()));
		}

		for (int i = 0; i < nameMods.getNameParts().size(); i++)
		{
			StartElement sE = eventFactory.createStartElement(prefix, uri, "namePart");

			eventWriter.add(sE);
			if (nameMods.getNameParts().get(i).getType() != null)
			{
				eventWriter.add(eventFactory.createAttribute("type", nameMods.getNameParts().get(i).getType()));
			}
			Characters characters = eventFactory.createCharacters(nameMods.getNameParts().get(i).getNamePart());
			eventWriter.add(characters);

			eventWriter.add(eventFactory.createEndElement(prefix, uri, "namePart"));

		}
		if (nameMods.getAffiliation() != null)
		{
			StartElement sE = eventFactory.createStartElement(prefix, uri, "affiliation");

			eventWriter.add(sE);

			Characters characters = eventFactory.createCharacters(nameMods.getAffiliation());
			eventWriter.add(characters);

			eventWriter.add(eventFactory.createEndElement(prefix, uri, "affiliation"));

		}
		if (nameMods.getRoleMods() != null)
		{
			StartElement sE = eventFactory.createStartElement(prefix, uri, "role");

			eventWriter.add(sE);

			if (nameMods.getRoleMods().getRoleTerm() != null)
			{
				StartElement sE2 = eventFactory.createStartElement(prefix, uri, "roleTerm");


				eventWriter.add(sE2);

				if (nameMods.getRoleMods().getAuthority() != null)
				{
					eventWriter.add(eventFactory.createAttribute("authority", nameMods.getRoleMods().getAuthority()));
				}
				if (nameMods.getRoleMods().getType() != null)
				{
					eventWriter.add(eventFactory.createAttribute("type", nameMods.getRoleMods().getType()));
				}

				Characters characters = eventFactory.createCharacters(nameMods.getRoleMods().getRoleTerm());
				eventWriter.add(characters);

				eventWriter.add(eventFactory.createEndElement(prefix, uri, "roleTerm"));

			}


			eventWriter.add(eventFactory.createEndElement(prefix, uri, "role"));

		}

		

		if (nameMods.getDescription() != null)
		{
			StartElement sE = eventFactory.createStartElement(prefix, uri, "description");

			eventWriter.add(sE);

			Characters characters = eventFactory.createCharacters(nameMods.getDescription());
			eventWriter.add(characters);

			eventWriter.add(eventFactory.createEndElement(prefix, uri, "description"));

		}
		eventWriter.add(eventFactory.createEndElement(prefix, uri, "name"));


	}

	/**
	 * Creates the node.
	 * @param eventWriter the event writer
	 * @param name the name
	 * @param originInfo the origin info
	 * @param prefix the prefix
	 * @param uri the uri
	 * @throws XMLStreamException the xML stream exception
	 */
	private void createModsOriginInfoNode(final XMLEventWriter eventWriter, final String name, final OriginInfo originInfo,
			final String prefix, final String uri) throws XMLStreamException
	{
		XMLEventFactory eventFactory = XMLEventFactory.newInstance();
		// Create Start node
		StartElement sElement = eventFactory.createStartElement(prefix, uri, name);

		eventWriter.add(sElement);


		if (originInfo.getDateCreated() != null)
		{
			StartElement sE = eventFactory.createStartElement(prefix, uri, "dateCreated");
			eventWriter.add(sE);
			eventWriter.add(eventFactory.createAttribute("encoding", _encoding));

			Characters characters = eventFactory.createCharacters(originInfo.getDateCreated().toString());
			eventWriter.add(characters);

			eventWriter.add(eventFactory.createEndElement(prefix, uri, "dateCreated"));

		}
		if (originInfo.getDateCreatedTimespan() != null)
		{
			if (originInfo.getDateCreatedTimespan().getDateFrom() != null)
			{
				StartElement sE = eventFactory.createStartElement(prefix, uri, "dateCreated");
				eventWriter.add(sE);
				eventWriter.add(eventFactory.createAttribute("encoding", _encoding));
				eventWriter.add(eventFactory.createAttribute("point", "start"));

				Characters characters = eventFactory.createCharacters(originInfo.getDateCreatedTimespan().getDateFrom()
						.toString());
				eventWriter.add(characters);

				eventWriter.add(eventFactory.createEndElement(prefix, uri, "dateCreated"));

			}
			if (originInfo.getDateCreatedTimespan().getDateTo() != null)
			{
				StartElement sE = eventFactory.createStartElement(prefix, uri, "dateCreated");
				eventWriter.add(sE);
				eventWriter.add(eventFactory.createAttribute("encoding", _encoding));
				eventWriter.add(eventFactory.createAttribute("point", "end"));

				Characters characters = eventFactory.createCharacters(originInfo.getDateCreatedTimespan().getDateTo()
						.toString());
				eventWriter.add(characters);

				eventWriter.add(eventFactory.createEndElement(prefix, uri, "dateCreated"));

			}
		}
		if (originInfo.getDateIssued() != null)
		{
			StartElement sE = eventFactory.createStartElement(prefix, uri, "dateIssued");
			eventWriter.add(sE);
			eventWriter.add(eventFactory.createAttribute("encoding", _encoding));

			Characters characters = eventFactory.createCharacters(originInfo.getDateIssued().toString());
			eventWriter.add(characters);

			eventWriter.add(eventFactory.createEndElement(prefix, uri, "dateIssued"));

		}
		if (originInfo.getDateIssuedTimespan() != null)
		{
			if (originInfo.getDateIssuedTimespan().getDateFrom() != null)
			{
				StartElement sE = eventFactory.createStartElement(prefix, uri, "dateIssued");
				eventWriter.add(sE);
				eventWriter.add(eventFactory.createAttribute("encoding", _encoding));
				eventWriter.add(eventFactory.createAttribute("point", "start"));

				Characters characters = eventFactory.createCharacters(originInfo.getDateIssuedTimespan().getDateFrom()
						.toString());
				eventWriter.add(characters);

				eventWriter.add(eventFactory.createEndElement(prefix, uri, "dateIssued"));

			}
			if (originInfo.getDateIssuedTimespan().getDateTo() != null)
			{
				StartElement sE = eventFactory.createStartElement(prefix, uri, "dateIssued");
				eventWriter.add(sE);
				eventWriter.add(eventFactory.createAttribute("encoding", _encoding));
				eventWriter.add(eventFactory.createAttribute("point", "end"));

				Characters characters = eventFactory.createCharacters(originInfo.getDateIssuedTimespan().getDateTo()
						.toString());
				eventWriter.add(characters);

				eventWriter.add(eventFactory.createEndElement(prefix, uri, "dateIssued"));

			}
		}
		if (originInfo.getDateCaptured() != null)
		{
			StartElement sE = eventFactory.createStartElement(prefix, uri, "dateCaptured");

			eventWriter.add(sE);
			eventWriter.add(eventFactory.createAttribute("encoding", _encoding));

			Characters characters = eventFactory.createCharacters(originInfo.getDateCaptured().toString());
			eventWriter.add(characters);

			eventWriter.add(eventFactory.createEndElement(prefix, uri, "dateCaptured"));

		}
		if (originInfo.getDateCapturedTimespan() != null)
		{
			if (originInfo.getDateCapturedTimespan().getDateFrom() != null)
			{
				StartElement sE = eventFactory.createStartElement(prefix, uri, "dateCaptured");

				eventWriter.add(sE);
				eventWriter.add(eventFactory.createAttribute("encoding", _encoding));
				eventWriter.add(eventFactory.createAttribute("point", "start"));

				Characters characters = eventFactory.createCharacters(originInfo.getDateCapturedTimespan()
						.getDateFrom().toString());
				eventWriter.add(characters);

				eventWriter.add(eventFactory.createEndElement(prefix, uri, "dateCaptured"));

			}
			if (originInfo.getDateCapturedTimespan().getDateTo() != null)
			{
				StartElement sE = eventFactory.createStartElement(prefix, uri, "dateCaptured");

				eventWriter.add(sE);
				eventWriter.add(eventFactory.createAttribute("encoding", _encoding));
				eventWriter.add(eventFactory.createAttribute("point", "end"));

				Characters characters = eventFactory.createCharacters(originInfo.getDateCapturedTimespan().getDateTo()
						.toString());
				eventWriter.add(characters);

				eventWriter.add(eventFactory.createEndElement(prefix, uri, "dateCaptured"));

			}
		}
		if (originInfo.getCopyrightDate() != null)
		{
			StartElement sE = eventFactory.createStartElement(prefix, uri, "copyrightDate");

			eventWriter.add(sE);
			eventWriter.add(eventFactory.createAttribute("encoding", _encoding));

			Characters characters = eventFactory.createCharacters(originInfo.getCopyrightDate().toString());
			eventWriter.add(characters);

			eventWriter.add(eventFactory.createEndElement(prefix, uri, "copyrightDate"));

		}
		if (originInfo.getCopyrightDateTimespan() != null)
		{
			if (originInfo.getCopyrightDateTimespan().getDateFrom() != null)
			{
				StartElement sE = eventFactory.createStartElement(prefix, uri, "copyrightDate");

				eventWriter.add(sE);
				eventWriter.add(eventFactory.createAttribute("encoding", _encoding));
				eventWriter.add(eventFactory.createAttribute("point", "start"));

				Characters characters = eventFactory.createCharacters(originInfo.getCopyrightDateTimespan()
						.getDateFrom().toString());
				eventWriter.add(characters);

				eventWriter.add(eventFactory.createEndElement(prefix, uri, "copyrightDate"));

			}
			if (originInfo.getCopyrightDateTimespan().getDateTo() != null)
			{
				StartElement sE = eventFactory.createStartElement(prefix, uri, "copyrightDate");

				eventWriter.add(sE);
				eventWriter.add(eventFactory.createAttribute("encoding", _encoding));
				eventWriter.add(eventFactory.createAttribute("point", "end"));

				Characters characters = eventFactory.createCharacters(originInfo.getCopyrightDateTimespan().getDateTo()
						.toString());
				eventWriter.add(characters);

				eventWriter.add(eventFactory.createEndElement(prefix, uri, "copyrightDate"));

			}
		}

		if (originInfo.getPublisher() != null)
		{
			StartElement sE = eventFactory.createStartElement(prefix, uri, "publisher");

			eventWriter.add(sE);

			Characters characters = eventFactory.createCharacters(originInfo.getPublisher());
			eventWriter.add(characters);

			eventWriter.add(eventFactory.createEndElement(prefix, uri, "publisher"));

		}

		if (originInfo.getPlaceTerm() != null)
		{
			StartElement sE = eventFactory.createStartElement(prefix, uri, "place");

			eventWriter.add(sE);


			StartElement sE2 = eventFactory.createStartElement(prefix, uri, "placeTerm");


			eventWriter.add(sE2);
			eventWriter.add(eventFactory.createAttribute("type", originInfo.getPlaceType()));

			Characters characters = eventFactory.createCharacters(originInfo.getPlaceTerm());
			eventWriter.add(characters);
			eventWriter.add(eventFactory.createEndElement(prefix, uri, "placeTerm"));


			eventWriter.add(eventFactory.createEndElement(prefix, uri, "place"));

		}
		if (originInfo.getEdition() != null)
		{
			StartElement sE = eventFactory.createStartElement(prefix, uri, "edition");

			eventWriter.add(sE);

			Characters characters = eventFactory.createCharacters(originInfo.getEdition());
			eventWriter.add(characters);

			eventWriter.add(eventFactory.createEndElement(prefix, uri, "edition"));

		}

		eventWriter.add(eventFactory.createEndElement(prefix, uri, name));

	}

	/**
	 * Creates the node.
	 * @param eventWriter the event writer
	 * @param name the name
	 * @param part the part
	 * @param prefix the prefix
	 * @param uri the uri
	 * @throws XMLStreamException the xML stream exception
	 */
	private void createModsRelatedItemNode(final XMLEventWriter eventWriter, final String name, final PartMods part,
			final String prefix, final String uri) throws XMLStreamException
	{
		XMLEventFactory eventFactory = XMLEventFactory.newInstance();
		// Create Start node
		StartElement sElement = eventFactory.createStartElement(prefix, uri, "part");
		eventWriter.add(sElement);


		if (part.getDetails() != null && !part.getDetails().isEmpty())
		{
			for (int i = 0; i < part.getDetails().size(); i++)
			{
				StartElement sE = eventFactory.createStartElement(prefix, uri, "detail");

				eventWriter.add(sE);
				if (part.getDetails().get(i).getType() != null)
				{
					eventWriter.add(eventFactory.createAttribute("type", part.getDetails().get(i).getType()));
				}
				if (part.getDetails().get(i).getNumber() != null)
				{
					sElement = eventFactory.createStartElement(prefix, uri, "number");
					eventWriter.add(sElement);
					Characters characters = eventFactory.createCharacters(part.getDetails().get(i).getNumber());
					eventWriter.add(characters);

					eventWriter.add(eventFactory.createEndElement(prefix, uri, "number"));


				}
				if (part.getDetails().get(i).getCaption() != null)
				{
					sElement = eventFactory.createStartElement(prefix, uri, "caption");
					eventWriter.add(sElement);
					Characters characters = eventFactory.createCharacters(part.getDetails().get(i).getCaption());
					eventWriter.add(characters);

					eventWriter.add(eventFactory.createEndElement(prefix, uri, "caption"));


				}
				eventWriter.add(eventFactory.createEndElement(prefix, uri, "detail"));

			}
		}
		if (part.getExtendsMods() != null && !part.getExtendsMods().isEmpty())
		{
			for (int i = 0; i < part.getExtendsMods().size(); i++)
			{
				StartElement sE = eventFactory.createStartElement(prefix, uri, "extent");

				eventWriter.add(sE);
				if (part.getDetails().get(i).getType() != null)
				{
					eventWriter.add(eventFactory.createAttribute("unit", part.getExtendsMods().get(i).getUnit()));
				}
				if (part.getExtendsMods().get(i).getStart() != null)
				{
					sElement = eventFactory.createStartElement(prefix, uri, "start");
					eventWriter.add(sElement);
					Characters characters = eventFactory.createCharacters(part.getExtendsMods().get(i).getStart());
					eventWriter.add(characters);

					eventWriter.add(eventFactory.createEndElement(prefix, uri, "start"));


				}
				if (part.getExtendsMods().get(i).getEnd() != null)
				{
					sElement = eventFactory.createStartElement(prefix, uri, "end");
					eventWriter.add(sElement);
					Characters characters = eventFactory.createCharacters(part.getExtendsMods().get(i).getEnd());
					eventWriter.add(characters);

					eventWriter.add(eventFactory.createEndElement(prefix, uri, "end"));


				}
				eventWriter.add(eventFactory.createEndElement(prefix, uri, "extent"));

			}
		}
		if (part.getDates() != null && !part.getDates().isEmpty())
		{
			for (int i = 0; i < part.getDates().size(); i++)
			{
				StartElement sE = eventFactory.createStartElement(prefix, uri, "date");

				eventWriter.add(sE);

				Characters characters = eventFactory.createCharacters(part.getDates().get(i).toString());
				eventWriter.add(characters);

				eventWriter.add(eventFactory.createEndElement(prefix, uri, "date"));

			}
		}

		eventWriter.add(eventFactory.createEndElement(prefix, uri, "part"));


	}

	/**
	 * Creates the node.
	 * @param eventWriter the event writer
	 * @param name the name
	 * @param place the place
	 * @throws XMLStreamException the xML stream exception
	 */
	private void createAspectPlaceNode(final XMLEventWriter eventWriter, final String name, final Place place)
			throws XMLStreamException
	{
		XMLEventFactory eventFactory = XMLEventFactory.newInstance();
		// Create Start node
		StartElement sElement = eventFactory.createStartElement("aodl", "http://pdr.bbaw.de/namespaces/aodl/", name);

		eventWriter.add(sElement);

		if (place.getType() != null)
		{
			eventWriter.add(eventFactory.createAttribute("type", place.getType()));

		}
		if (place.getSubtype() != null)
		{
			eventWriter.add(eventFactory.createAttribute("subtype", place.getSubtype()));

		}
		if (place.getKey() != null)
		{
			eventWriter.add(eventFactory.createAttribute("key", place.getKey()));

		}
		// Create Content
		if (place.getPlaceName() != null)
		{
			Characters characters = eventFactory.createCharacters(place.getPlaceName());
			eventWriter.add(characters);

		}
		eventWriter.add(eventFactory.createEndElement("aodl", "http://pdr.bbaw.de/namespaces/aodl/", "place"));


	}

	/**
	 * Creates the node.
	 * @param eventWriter the event writer
	 * @param name the name
	 * @param r the Reference
	 * @param prefix the prefix
	 * @param uri the uri
	 * @throws XMLStreamException the xML stream exception
	 */
	private void createModsNode(final XMLEventWriter eventWriter, final String name, final ReferenceMods r,
			final String prefix, final String uri) throws XMLStreamException
	{
		XMLEventFactory eventFactory = XMLEventFactory.newInstance();

		// Create config open tag
		StartElement startElement = eventFactory.createStartElement(prefix, uri, "mods");
		eventWriter.add(startElement);
		// add display name to reference node
		// TODO nicht lieber pdrID?
		eventWriter.add(eventFactory.createAttribute("xmlns:mods", "http://www.loc.gov/mods/v3"));

		eventWriter.add(eventFactory.createAttribute("xmlns:xsi", "http://www.w3.org/2001/XMLSchema-instance"));
		eventWriter.add(eventFactory.createAttribute("xsi:schemaLocation",
				"http://pdr.bbaw.de/namespaces/rodl/ http://pdr.bbaw.de/schema/rodl_mods.xsd"));
		if (!r.getPdrId().getType().equals("genre"))
		{
			eventWriter.add(eventFactory.createAttribute("ID", r.getPdrId().toString()));
		}



		// Write the different nodes

		if (r.getTitleInfo() != null)
		{
			startElement = eventFactory.createStartElement(prefix, uri, "titleInfo");
			eventWriter.add(startElement);

			if (r.getTitleInfo() != null && r.getTitleInfo().getTitle() != null)
			{

				createModsTitleInfoNode(eventWriter, "title", r.getTitleInfo().getTitle(), prefix, uri);

			}
			if (r.getTitleInfo() != null && r.getTitleInfo().getSubTitle() != null)
			{

				createModsTitleInfoNode(eventWriter, "subTitle", r.getTitleInfo().getSubTitle(), prefix, uri);

			}
			if (r.getTitleInfo() != null && r.getTitleInfo().getPartNumber() != null)
			{
				createModsTitleInfoNode(eventWriter, "partNumber", r.getTitleInfo().getPartNumber(), prefix, uri);

			}
			if (r.getTitleInfo() != null && r.getTitleInfo().getPartName() != null)
			{
				createModsTitleInfoNode(eventWriter, "partName", r.getTitleInfo().getPartName(), prefix, uri);

			}

			eventWriter.add(eventFactory.createEndElement(prefix, uri, "titleInfo"));

		}
		if (r.getNameMods() != null)
		{
			for (int i = 0; i < r.getNameMods().size(); i++)
			{
				createModsNameNode(eventWriter, "name", r.getNameMods().get(i), prefix, uri);
			}
		}

		if (r.getGenre() != null)
		{
			StartElement sE = eventFactory.createStartElement(prefix, uri, "genre");
			eventWriter.add(sE);
			if (r.getGenre().getAuthority() != null)
			{
				eventWriter.add(eventFactory.createAttribute("authority", r.getGenre().getAuthority()));
			}
			Characters characters = eventFactory.createCharacters(r.getGenre().getGenre());
			eventWriter.add(characters);

			eventWriter.add(eventFactory.createEndElement(prefix, uri, "genre"));

		}

		if (r.getOriginInfo() != null)
		{
			createModsOriginInfoNode(eventWriter, "originInfo", r.getOriginInfo(), prefix, uri);
		}

		if (r.getNote() != null)
		{
			StartElement sE = eventFactory.createStartElement(prefix, uri, "note");
			eventWriter.add(sE);
			if (r.getNote().getType() != null)
			{
				eventWriter.add(eventFactory.createAttribute("type", r.getNote().getType()));
			}
			Characters characters = eventFactory.createCharacters(r.getNote().getNote());
			eventWriter.add(characters);

			eventWriter.add(eventFactory.createEndElement(prefix, uri, "note"));

		}

		if (r.getIdentifiersMods() != null && !r.getIdentifiersMods().isEmpty())
		{
			for (int i = 0; i < r.getIdentifiersMods().size(); i++)
			{
				if (r.getIdentifiersMods().get(i).getIdentifier() != null && !"".equals(r.getIdentifiersMods().get(i).getIdentifier()))
				{
					StartElement sE = eventFactory.createStartElement(prefix, uri, "identifier");
					eventWriter.add(sE);
					if (r.getIdentifiersMods().get(i).getType() != null)
					{
						eventWriter.add(eventFactory.createAttribute("type", r.getIdentifiersMods().get(i).getType()));
					}
					else
					{
						eventWriter.add(eventFactory.createAttribute("type", "pdr"));
					}
					Characters characters = eventFactory.createCharacters(r.getIdentifiersMods().get(i).getIdentifier());
					eventWriter.add(characters);
	
					eventWriter.add(eventFactory.createEndElement(prefix, uri, "identifier"));
				}

			}
		}

		if (r.getLocation() != null)
		{
			StartElement sE = eventFactory.createStartElement(prefix, uri, "location");
			eventWriter.add(sE);



			if (r.getLocation().getPhysicalLocation() != null)
			{
				StartElement sE2 = eventFactory.createStartElement(prefix, uri, "physicalLocation");

				eventWriter.add(sE2);
				Characters characters = eventFactory.createCharacters(r.getLocation().getPhysicalLocation());
				eventWriter.add(characters);
				eventWriter.add(eventFactory.createEndElement(prefix, uri, "physicalLocation"));

			}
			if (r.getLocation().getShelfLocator() != null)
			{
				StartElement sE2 = eventFactory.createStartElement(prefix, uri, "shelfLocator");

				eventWriter.add(sE2);
				Characters characters = eventFactory.createCharacters(r.getLocation().getShelfLocator());
				eventWriter.add(characters);
				eventWriter.add(eventFactory.createEndElement(prefix, uri, "shelfLocator"));

			}
			if (r.getLocation().getUrl() != null)
			{
				StartElement sE2 = eventFactory.createStartElement(prefix, uri, "url");

				eventWriter.add(sE2);
				Characters characters = eventFactory.createCharacters(r.getLocation().getUrl());
				eventWriter.add(characters);
				eventWriter.add(eventFactory.createEndElement(prefix, uri, "url"));

			}
			eventWriter.add(eventFactory.createEndElement(prefix, uri, "location"));

		}

		if (r.getAccessCondition() != null)
		{
			StartElement sE = eventFactory.createStartElement(prefix, uri, "accessCondition");
			eventWriter.add(sE);
			if (r.getAccessCondition().getAccessCondition() != null)
			{
				eventWriter.add(eventFactory.createAttribute("type", r.getAccessCondition().getType()));
			}
			Characters characters = eventFactory.createCharacters(r.getAccessCondition().getAccessCondition());
			eventWriter.add(characters);

			eventWriter.add(eventFactory.createEndElement(prefix, uri, "accessCondition"));

		}
		// if reference is part of series, write that into <relatedItem> element
		if (r.getSeriesTitleInfo() != null)
		{
			StartElement sE = eventFactory.createStartElement(prefix, uri, "relatedItem");
			eventWriter.add(sE);
			eventWriter.add(eventFactory.createAttribute("type", "series"));

			// XXX rodl_mods.xsd violates actual MODS by requiring TitleInfo to contain exactly
			// one title element. FIXME: should this better be handled at repo sync?
			// This conforms to that violation so nothing goes wrong:
			if (r.getSeriesTitleInfo().getTitle() != null) {
			
				startElement = eventFactory.createStartElement(prefix, uri, "titleInfo");
				eventWriter.add(startElement);

				createModsTitleInfoNode(eventWriter, "title", r.getSeriesTitleInfo().getTitle(), prefix, uri);

				if (r.getSeriesTitleInfo().getSubTitle() != null)
					createModsTitleInfoNode(eventWriter, "subTitle", r.getSeriesTitleInfo().getSubTitle(), prefix, uri);

				if (r.getSeriesTitleInfo().getPartNumber() != null)
					createModsTitleInfoNode(eventWriter, "partNumber", r.getSeriesTitleInfo().getPartNumber(), prefix, uri);

				if (r.getSeriesTitleInfo().getPartName() != null)
					createModsTitleInfoNode(eventWriter, "partName", r.getSeriesTitleInfo().getPartName(), prefix, uri);


				eventWriter.add(eventFactory.createEndElement(prefix, uri, "titleInfo"));

			}
			
			eventWriter.add(eventFactory.createEndElement(prefix, uri, "relatedItem"));

		}
		if (r.getRelatedItems() != null && !r.getRelatedItems().isEmpty())
		{
			for (RelatedItem relItem : r.getRelatedItems())
			{
				StartElement sE = eventFactory.createStartElement(prefix, uri, "relatedItem");
				eventWriter.add(sE);
				if (relItem.getType() != null)
				{
					eventWriter.add(eventFactory.createAttribute("type", relItem.getType()));
				}
				if (relItem.getId() != null)
				{
					eventWriter.add(eventFactory.createAttribute("ID", relItem.getId()));
				}
				if (relItem.getPart() != null)
				{
					createModsRelatedItemNode(eventWriter, "part", relItem.getPart(), prefix, uri);
				}
				

				eventWriter.add(eventFactory.createEndElement(prefix, uri, "relatedItem"));

			}

		}

		if (r.getRecord() != null)
		{
			createNodeNoNamespace(eventWriter, "recordInfo", r.getRecord(), prefix, uri);
		}

		eventWriter.add(eventFactory.createEndElement(prefix, uri, "mods"));


	}

	/**
	 * Creates the node.
	 * @param eventWriter the event writer
	 * @param name the name
	 * @param relation the relation
	 * @param relationStm 
	 * @throws XMLStreamException the xML stream exception
	 */
	private Vector<XMLEvent> createAspectRelationNode(final XMLEventWriter eventWriter, final String name, final Relation relation, RelationStm relationStm)
			throws XMLStreamException
	{
		// assemble xml event list, but don't write it to stream yet,
		// as we don't want to append no invalid relation element
		// and need to let relationStm know if it even has valid
		// sub elements
		Vector<XMLEvent> relXmlEvents = new Vector<XMLEvent>();
		XMLEventFactory eventFactory = XMLEventFactory.newInstance();
		// Create Start node
		StartElement sElement = eventFactory.createStartElement("aodl", "http://pdr.bbaw.de/namespaces/aodl/", name);

		relXmlEvents.add(sElement);

		// attributes object, provider are required
		// @object
		if (relation.getObject() == null) {
			buflog("MODS Model violation: no object attribute in relation element!!");
			return null;
			//eventWriter.add(eventFactory.createAttribute("object", relationStm.getSubject().toString())); // XXX oh, shit!
		} else 
			relXmlEvents.add(eventFactory.createAttribute("object", relation.getObject().toString()));
		
		// @provider
		if (relation.getProvider() == null)	{
			buflog("MODS Model violation: no provider attribute in relation element!!");
			return null;
		} else 
			relXmlEvents.add(eventFactory.createAttribute("provider", relation.getProvider()));
		
		if (relation.getRClass() != null)
			relXmlEvents.add(eventFactory.createAttribute("class", relation.getRClass()));

		if (relation.getContext() != null)
			relXmlEvents.add(eventFactory.createAttribute("context", relation.getContext()));

		
		// Create Content
		if (relation.getRelation() != null) {
			Characters characters = eventFactory.createCharacters(relation.getRelation());
			relXmlEvents.add(characters);
		}
		relXmlEvents.add(eventFactory.createEndElement("aodl", "http://pdr.bbaw.de/namespaces/aodl/", "relation"));
		
		return relXmlEvents;
	}

	/**
	 * Creates the node.
	 * @param eventWriter the event writer
	 * @param name the name
	 * @param relStm the relationStatement
	 * @throws XMLStreamException the xML stream exception
	 */
	private void createAspectRelationStmNode(final XMLEventWriter eventWriter, final String name, final RelationStm relStm)
			throws XMLStreamException
	{
		// queue xml events up before writing to stream, in case
		// sub elements violate model
		Vector<XMLEvent> relStmXmlEvents = new Vector<XMLEvent>(); 
		
		XMLEventFactory eventFactory = XMLEventFactory.newInstance();
		// Create Start node
		StartElement sElement = eventFactory.createStartElement("aodl", "http://pdr.bbaw.de/namespaces/aodl/", name);
		
		relStmXmlEvents.add(sElement);
		
		if (relStm.getSubject() == null) {
			buflog("aodl schema violation: relationStm without subject attribute!");
		} else
			relStmXmlEvents.add(eventFactory.createAttribute("subject", relStm.getSubject().toString()));
	
		// Create subelements
		if (relStm.getRelations() != null) {
			// queue up sub element xml events separately
			for (Relation rel : relStm.getRelations()) {
				Vector<XMLEvent> relXmlElements = createAspectRelationNode(eventWriter, "relation", rel, relStm);
				if (relXmlElements != null) // 
					relStmXmlEvents.addAll(relXmlElements);
			}
		} else // don't append this relationStm node to xml
			return;
		
		// Create End node
		EndElement eElement = eventFactory.createEndElement("aodl", "http://pdr.bbaw.de/namespaces/aodl/", name);
		relStmXmlEvents.add(eElement);

		// write relationStm xml to stream
		for (XMLEvent e : relStmXmlEvents)
			eventWriter.add(e);
	}

	/**
	 * Creates the node.
	 * @param eventWriter the event writer
	 * @param name the name
	 * @param r the revision
	 * @param prefix the prefix
	 * @param uri the uri
	 * @throws XMLStreamException the xML stream exception
	 */
	private void createPDRObjectRelationNode(final XMLEventWriter eventWriter, final String name, final Revision r, final String prefix,
			final String uri) throws XMLStreamException
	{
		XMLEventFactory eventFactory = XMLEventFactory.newInstance();
		// Create Start node
		StartElement sElement = eventFactory.createStartElement(prefix, uri, name);

		eventWriter.add(sElement);
		eventWriter.add(eventFactory.createAttribute("ref", new Integer(r.getRef()).toString()));
		eventWriter
				.add(eventFactory.createAttribute("timestamp", _adminDateFormat.format(r.getTimeStamp()).toString()));
		eventWriter.add(eventFactory.createAttribute("authority", r.getAuthority().toString()));
		// TODO das Schema sieht keinen authority namen mehr vor, änderung im
		// model umsetzen.
		// // Create Content
		// Characters characters =
		// eventFactory.createCharacters(r.getRevisor());
		// eventWriter.add(characters);
		// Create End node
		EndElement eElement = eventFactory.createEndElement(prefix, uri, name);
		eventWriter.add(eElement);

	}

	/**
	 * Creates the node.
	 * @param eventWriter the event writer
	 * @param name the name
	 * @param semStm the semantic Statement
	 * @throws XMLStreamException the xML stream exception
	 */
	private void createAspectSemanticStmNode(final XMLEventWriter eventWriter, final String name, final SemanticStm semStm)
			throws XMLStreamException
	{
		XMLEventFactory eventFactory = XMLEventFactory.newInstance();
		// Create Start node
		StartElement sElement = eventFactory.createStartElement("aodl", "http://pdr.bbaw.de/namespaces/aodl/", name);

		eventWriter.add(sElement);
		if (semStm.getProvider() != null)
		{
			eventWriter.add(eventFactory.createAttribute("provider", semStm.getProvider()));
		}

		// Create Content
		if (semStm.getLabel() != null)
		{
			Characters characters = eventFactory.createCharacters(semStm.getLabel());
			eventWriter.add(characters);

		}
		// Create End node
		EndElement eElement = eventFactory.createEndElement("aodl", "http://pdr.bbaw.de/namespaces/aodl/", name);
		eventWriter.add(eElement);


	}

	/**
	 * Writes an XML element representing an {@link Aspect}'s {@link SpatialStm} .
	 * @param eventWriter the event writer
	 * @param name the name
	 * @param spaStm the spatial Statement
	 * @throws XMLStreamException the xML stream exception
	 */
	private void createSpatialStmNode(final XMLEventWriter eventWriter, final String name, final SpatialStm spaStm)
			throws XMLStreamException
	{
		XMLEventFactory eventFactory = XMLEventFactory.newInstance();
		// Create Start node
		StartElement sElement = eventFactory.createStartElement("aodl", "http://pdr.bbaw.de/namespaces/aodl/", name);

		eventWriter.add(sElement);
		// if spatialStm has sub nodes,
		// its type probably shouldn't be 'undefined'. So change this
		if (spaStm.getType() != null) {
			if (spaStm.getType().equals("undefined"))
				if (spaStm.getPlaces() != null && !spaStm.getPlaces().isEmpty())
					spaStm.setType("defined");
		} else spaStm.setType("defined");
		eventWriter.add(eventFactory.createAttribute("type", spaStm.getType()));
		
		// Create Content
		if (spaStm.getPlaces() != null)
		{
			for (int j = 0; j < spaStm.getPlaces().size(); j++)
			{
				createAspectPlaceNode(eventWriter, "place", spaStm.getPlaces().get(j));

			}

		}
		// Create End node
		EndElement eElement = eventFactory.createEndElement("aodl", "http://pdr.bbaw.de/namespaces/aodl/", name);
		eventWriter.add(eElement);


	}

	/**
	 * Creates the node.
	 * @param eventWriter the event writer
	 * @param name the name
	 * @param value the value
	 * @param lang the lang
	 * @throws XMLStreamException the xML stream exception
	 */
	private void createModsTemplateDocPartNode(final XMLEventWriter eventWriter, final String name, final String value, final String lang)
			throws XMLStreamException
	{
		XMLEventFactory eventFactory = XMLEventFactory.newInstance();
		// Create Start node
		StartElement sElement = eventFactory.createStartElement("", "", name);

		eventWriter.add(sElement);
		eventWriter.add(eventFactory.createAttribute("xml:lang", lang));


		if (value.trim().length() > 0)
		{
			Characters characters = eventFactory.createCharacters(value.trim());
			eventWriter.add(characters);
		}
		eventWriter.add(eventFactory.createEndElement("", "", name));


	}

	/**
	 * Creates a sub node of a MODS titleInfo element.
	 * @param eventWriter the event writer
	 * @param name e.g. 'subTitle', 'title', 'partNumber'...
	 * @param text the text
	 * @param prefix the prefix
	 * @param uri the uri
	 * @throws XMLStreamException the xML stream exception
	 */
	private void createModsTitleInfoNode(final XMLEventWriter eventWriter, final String name, final String text,
			final String prefix, final String uri) throws XMLStreamException
	{
		XMLEventFactory eventFactory = XMLEventFactory.newInstance();
		// Create Start node
		StartElement sElement = eventFactory.createStartElement(prefix, uri, name);

		eventWriter.add(sElement);
		Characters characters = eventFactory.createCharacters(text);
		eventWriter.add(characters);
		eventWriter.add(eventFactory.createEndElement(prefix, uri, name));


	}

	/**
	 * Creates the node.
	 * @param eventWriter the event writer
	 * @param name the name
	 * @param tStm the time Statement
	 * @throws XMLStreamException the xML stream exception
	 */
	private void createAspectTimeStmNode(final XMLEventWriter eventWriter, final String name, final TimeStm tStm)
			throws XMLStreamException
	{
		XMLEventFactory eventFactory = XMLEventFactory.newInstance();
		// Create Start node
		StartElement sElement = eventFactory.createStartElement("aodl", "http://pdr.bbaw.de/namespaces/aodl/", name);

		eventWriter.add(sElement);
		// if node contains sub ndoes, it shouldnt be 'undefined'
		if (tStm.getType() != null) {
			if (tStm.getType().equals("undefined"))
				if (tStm.getTimes() != null && !tStm.getTimes().isEmpty())
					tStm.setType("defined");
		} else tStm.setType("defined");
		eventWriter.add(eventFactory.createAttribute("type", tStm.getType()));

		// Create Content
		if (tStm.getTimes() != null)
		{
			for (int j = 0; j < tStm.getTimes().size(); j++)
			{
				StartElement startElement = eventFactory.createStartElement("aodl",
						"http://pdr.bbaw.de/namespaces/aodl/", "time");
				eventWriter.add(startElement);

				if (tStm.getTimes().get(j).getAccuracy() != null)
				{
					eventWriter.add(eventFactory.createAttribute("accuracy", tStm.getTimes().get(j).getAccuracy()));

				}
				if (tStm.getTimes().get(j).getType() != null)
				{
					eventWriter.add(eventFactory.createAttribute("type", tStm.getTimes().get(j).getType()));

				}
				// Create Content
				if (tStm.getTimes().get(j).getTimeStamp() != null)
				{
					Characters characters = eventFactory.createCharacters(tStm.getTimes().get(j).getTimeStamp()
							.toString());
					eventWriter.add(characters);

				}
				eventWriter.add(eventFactory.createEndElement("aodl", "http://pdr.bbaw.de/namespaces/aodl/", "time"));

			}

		}
		// Create End node
		EndElement eElement = eventFactory.createEndElement("aodl", "http://pdr.bbaw.de/namespaces/aodl/", name);
		eventWriter.add(eElement);


	}

	/**
	 * Creates the node.
	 * @param eventWriter the event writer
	 * @param name the name
	 * @param validationStm the validation statement
	 * @param prefix the prefix
	 * @param uri the uri
	 * @param pdrObject 
	 * @throws XMLStreamException the xML stream exception
	 */
	private void createValidationStmNode(final XMLEventWriter eventWriter, final String name, final ValidationStm validationStm,
			final String prefix, final String uri, PdrMetaObject pdrObject) throws XMLStreamException
	{
		// create validationStm element
		XMLEventFactory eventFactory = XMLEventFactory.newInstance();
		// Create Start node
		StartElement sElement = eventFactory.createStartElement(prefix, uri, name);
		
		eventWriter.add(sElement);
		String auth = null;
		if (validationStm.getAuthority() == null) {
			buflog("Aodl warning: validationStm without authority. falling back to revision authority");  
			// XXX: first or last revision?
			auth = pdrObject.getRecord().getRevisions().get(0).getAuthority().toString();
		} else 
			auth = validationStm.getAuthority().toString();
		eventWriter.add(eventFactory.createAttribute("authority", auth));


		if (validationStm.getReference() != null) {
			// XXX aodl schema actually does not limit references to only one per validationStm...
			Reference ref = validationStm.getReference();
			// <reference>
			sElement = eventFactory.createStartElement(prefix, uri, "reference");

			eventWriter.add(sElement);
			if (ref.getInternal() != null)
				eventWriter.add(eventFactory.createAttribute("internal", ref.getInternal()));

			// @quality
			if (ref.getQuality() != null) // XXX aodl schema does actually not require quality attribute, but rodl editor does...
				eventWriter.add(eventFactory.createAttribute("quality", ref.getQuality()));

			// authority attribute is not even a part in aodl schema reference definition...!
			// but it is in podl schema!!!
			// @authority - only if serializing Person object
			if (pdrObject instanceof Person)
				if (ref.getAuthority() != null) {
					eventWriter.add(eventFactory.createAttribute("authority", ref.getAuthority().toString()));
				} else
					eventWriter.add(eventFactory.createAttribute("authority", auth));

			// Create Content
			if (ref.getSourceId() != null) {
				Characters characters = eventFactory.createCharacters(ref.getSourceId().toString());
				eventWriter.add(characters);
			} else 
				buflog("Aodl violation: no source Id in reference elements!");
			
			EndElement eElement = eventFactory.createEndElement(prefix, uri, "reference");
			eventWriter.add(eElement);
		}

		sElement = eventFactory.createStartElement(prefix, uri, "interpretation");
		eventWriter.add(sElement);

		if (validationStm.getInterpretation() != null) {
			Characters characters = eventFactory.createCharacters(validationStm.getInterpretation());
			eventWriter.add(characters);
		}
		EndElement eElement = eventFactory.createEndElement(prefix, uri, "interpretation");
		eventWriter.add(eElement);


		// Create End node
		eElement = eventFactory.createEndElement(prefix, uri, name);
		eventWriter.add(eElement);


	}

	/**
	 * Creates the node.
	 * @param eventWriter the event writer
	 * @param tr the tagging range
	 * @param text the text
	 * @throws XMLStreamException the xML stream exception
	 */
	private void createAspectMarkupNode(final XMLEventWriter eventWriter, final TaggingRange tr, String text)
			throws XMLStreamException
	{
		XMLEventFactory eventFactory = XMLEventFactory.newInstance();
		// Create Start node
		StartElement sElement = eventFactory.createStartElement("aodl", "http://pdr.bbaw.de/namespaces/aodl/",
				tr.getName());

		eventWriter.add(sElement);
		if (tr.getType() != null && tr.getType().length() > 0)
		{
			eventWriter.add(eventFactory.createAttribute("type", tr.getType()));
		}
		else
		{
			eventWriter.add(eventFactory.createAttribute("type", "undefined"));
		}
		if (tr.getSubtype() != null && tr.getSubtype().length() > 0)
		{
			eventWriter.add(eventFactory.createAttribute("subtype", tr.getSubtype()));
		}
		if (tr.getRole() != null && tr.getRole().length() > 0)
		{
			eventWriter.add(eventFactory.createAttribute("role", tr.getRole()));
		}
		if (tr.getAna() != null && tr.getAna().length() > 0)
		{
			eventWriter.add(eventFactory.createAttribute("ana", tr.getAna()));
		}

		if (tr.getKey() != null && tr.getKey().length() > 0)
		{
			eventWriter.add(eventFactory.createAttribute("key", tr.getKey()));
		}
		if (tr.getWhen() != null)
		{
			eventWriter.add(eventFactory.createAttribute("when", tr.getWhen().toString()));
		}
		if (tr.getFrom() != null)
		{
			eventWriter.add(eventFactory.createAttribute("from", (tr.getFrom().toString())));
		}
		if (tr.getTo() != null)
		{
			eventWriter.add(eventFactory.createAttribute("to", tr.getTo().toString()));
		}
		if (tr.getNotBefore() != null)
		{
			eventWriter.add(eventFactory.createAttribute("notBefore", tr.getNotBefore().toString()));
		}
		if (tr.getNotAfter() != null)
		{
			eventWriter.add(eventFactory.createAttribute("notAfter", tr.getNotAfter().toString()));
		}

		// FIXME Workaround
		text = text + " ";
		// buflog("injester, tr.start " + tr.getStart() + " ln " +
		// tr.getLength());
		String subText = text.substring(tr.getStart(), Math.min(tr.getStart() + tr.getLength(), text.length()));
		Characters characters = eventFactory.createCharacters(subText);
		eventWriter.add(characters);

		EndElement eElement = eventFactory
				.createEndElement("aodl", "http://pdr.bbaw.de/namespaces/aodl/", tr.getName());
		eventWriter.add(eElement);

	}

	/**
	 * Creates the node no namespace.
	 * @param eventWriter the event writer
	 * @param name the name
	 * @param record the record
	 * @param prefix the prefix
	 * @param uri the uri
	 * @throws XMLStreamException the xML stream exception
	 */
	private void createNodeNoNamespace(final XMLEventWriter eventWriter, final String name, final Record record,
			final String prefix, final String uri) throws XMLStreamException
	{
		XMLEventFactory eventFactory = XMLEventFactory.newInstance();


		// Create Start node

		if (!record.getRevisions().isEmpty())
		{
			if (record.getRevisions().firstElement() != null
					&& record.getRevisions().firstElement().getTimeStamp() != null
					&& record.getRevisions().firstElement().getAuthority() != null)
			{
				StartElement sE = eventFactory.createStartElement(prefix, uri, name);
				eventWriter.add(sE);


				StartElement sE2 = eventFactory.createStartElement(prefix, uri, "recordCreationDate");

				eventWriter.add(sE2);
				Characters characters;
				eventWriter.add(eventFactory.createAttribute("encoding", _encoding));

				characters = eventFactory.createCharacters(_adminDateFormat.format(record.getRevisions().firstElement()
						.getTimeStamp()));
				eventWriter.add(characters);

				eventWriter.add(eventFactory.createEndElement(prefix, uri, "recordCreationDate"));


				sE2 = eventFactory.createStartElement(prefix, uri, "recordContentSource");

				eventWriter.add(sE2);
				eventWriter.add(eventFactory.createAttribute("authority", "PDR"));
				characters = eventFactory.createCharacters(record.getRevisions().firstElement().getAuthority()
						.toString());
				eventWriter.add(characters);

				eventWriter.add(eventFactory.createEndElement(prefix, uri, "recordContentSource"));


				eventWriter.add(eventFactory.createEndElement(prefix, uri, name));

			}

			if (record.getRevisions().size() > 1)
			{
				for (int j = 1; j < record.getRevisions().size(); j++)
				{
					if (record.getRevisions().get(j).getTimeStamp() != null
							&& record.getRevisions().get(j).getAuthority() != null)
					{
						StartElement sE = eventFactory.createStartElement(prefix, uri, name);
						eventWriter.add(sE);


						Characters characters;
						StartElement sE2 = eventFactory.createStartElement(prefix, uri, "recordContentSource");

						eventWriter.add(sE2);
						eventWriter.add(eventFactory.createAttribute("authority", "PDR"));

						characters = eventFactory.createCharacters(record.getRevisions().get(j).getAuthority()
								.toString());
						eventWriter.add(characters);

						eventWriter.add(eventFactory.createEndElement(prefix, uri, "recordContentSource"));

						sE2 = eventFactory.createStartElement(prefix, uri, "recordChangeDate");

						eventWriter.add(sE2);
						eventWriter.add(eventFactory.createAttribute("encoding", _encoding));

						characters = eventFactory.createCharacters(_adminDateFormat.format(record.getRevisions().get(j)
								.getTimeStamp()));
						eventWriter.add(characters);

						eventWriter.add(eventFactory.createEndElement(prefix, uri, "recordChangeDate"));



						eventWriter.add(eventFactory.createEndElement(prefix, uri, name));

					}
				}
			}
		}

	}

	/**
	 * Process append text with line breaks.
	 * @param eventWriter the event writer
	 * @param subText the sub text
	 * @throws XMLStreamException the xML stream exception
	 */
	private void processAppendTextWithLineBreaks(final XMLEventWriter eventWriter, final String subText)
			throws XMLStreamException
	{
		XMLEventFactory eventFactory = XMLEventFactory.newInstance();

		if (subText.contains("\n") || subText.contains("\r"))
		{
			String[] subs = subText.split("\\n|\\r");
			for (int i = 0; i < subs.length; i++)
			{
				String removeLB = subs[i].replace("\n", "");
				removeLB =  subs[i].replace("\r", "");
				Characters characters = eventFactory.createCharacters(removeLB);
				eventWriter.add(characters);

				if (i < subs.length - 1)
				{
					StartElement startElement = eventFactory.createStartElement("aodl",
							"http://pdr.bbaw.de/namespaces/aodl/", "lb");
					eventWriter.add(startElement);

					eventWriter.add(eventFactory.createEndElement("aodl", "http://pdr.bbaw.de/namespaces/aodl/", "lb"));
				}

			}
			if (subText.endsWith("\n") || subText.endsWith("\r"))
			{
				StartElement startElement = eventFactory.createStartElement("aodl",
						"http://pdr.bbaw.de/namespaces/aodl/", "lb");
				eventWriter.add(startElement);

				eventWriter.add(eventFactory.createEndElement("aodl", "http://pdr.bbaw.de/namespaces/aodl/", "lb"));
			}
		}
		else
		{
			Characters characters = eventFactory.createCharacters(subText);
			eventWriter.add(characters);
		}
	}

	/**
	 * @param a Aspect
	 * @return xml string
	 * @throws XMLStreamException xml stream exc.
	 * @see org.bbaw.pdr.ae.control.core.XMLProcessorInterface#writeToXML(org.bbaw.pdr.ae.model.Aspect)
	 */
	@Override
	public final String writeToXML(final Aspect a) throws XMLStreamException
	{
		this.logmsg = "";
		
		// Create a XMLOutputFactory
		XMLOutputFactory outputFactory = XMLOutputFactory.newInstance();
		// Create XMLEventWriter

		ByteArrayOutputStream bout = new ByteArrayOutputStream();

		XMLEventWriter eventWriter = outputFactory.createXMLEventWriter(bout, "UTF-8");

		// Create a EventFactory
		XMLEventFactory eventFactory = XMLEventFactory.newInstance();
		// Create and write Start Tag
		StartDocument startDocument = eventFactory.createStartDocument();
		eventWriter.add(startDocument);

		// Create config open tag
		StartElement startElement = eventFactory.createStartElement("aodl", "http://pdr.bbaw.de/namespaces/aodl/",
				"aspect");
		eventWriter.add(startElement);
		eventWriter.add(eventFactory.createNamespace("aodl", "http://pdr.bbaw.de/namespaces/aodl/"));

		eventWriter.add(eventFactory.createAttribute("xmlns:xsi", "http://www.w3.org/2001/XMLSchema-instance"));
		eventWriter.add(eventFactory.createAttribute("xsi:schemaLocation",
				"http://pdr.bbaw.de/namespaces/aodl/ http://pdr.bbaw.de/schema/aodl.xsd"));
		eventWriter.add(eventFactory.createAttribute("id", a.getPdrId().toString()));

		// add the display name to the aspect node
		// eventWriter.add(eventFactory.createAttribute("displayName",
		// a.getDisplayName()));

		//

		// Write the different nodes

		startElement = eventFactory.createStartElement("aodl", "http://pdr.bbaw.de/namespaces/aodl/", "record");
		eventWriter.add(startElement);

		for (int i = 0; i < a.getRecord().getRevisions().size(); i++)
		{

			createPDRObjectRelationNode(eventWriter, "revision", a.getRecord().getRevisions().get(i), "aodl",
					"http://pdr.bbaw.de/namespaces/aodl/");
		}
		eventWriter.add(eventFactory.createEndElement("aodl", "http://pdr.bbaw.de/namespaces/aodl/", "record"));


		// <timeDim> 
		startElement = eventFactory.createStartElement("aodl", "http://pdr.bbaw.de/namespaces/aodl/", "timeDim");
		eventWriter.add(startElement);
		// 	<timeStm>
		// aspect editor makes sure that each aspect has at least one timeStm element with legal type attribute,
		// thus fulfilling minimal requirement made in aodl schema. However, as soon as one ore more proper
		// timeStm elements, with time subnode and everything, are available, we don't need those fake dummy
		// timeStms anymore. Also, we don't need more than one dummy element.
		// therefore, we count the number of proper timeStms and then decide if we will serialize the dummy nodes
		TimeDim timeDim = a.getTimeDim();
		Vector<TimeStm> timeStms = new Vector<TimeStm>();
		if (timeDim != null && timeDim.getTimeStms() != null) 
			for (TimeStm timeStm : timeDim.getTimeStms()) 
				// assumption: only non-empty list of <time> sub elements constitutes valid non-empty timeStm element
				if (timeStm.getTimes() != null && !timeStm.getTimes().isEmpty())
					timeStms.add(timeStm);
		if (timeStms.isEmpty()){ // handle missing timeDim (unlikely) and fallback if no proper timeStm were found 
			TimeStm timeStm = new TimeStm();
			timeStm.setType("undefined");
			timeStms.add(timeStm);
		}
		// write timeStm nodes
		for (TimeStm timeStm : timeStms)
			createAspectTimeStmNode(eventWriter, "timeStm", timeStm);
		eventWriter.add(eventFactory.createEndElement("aodl", "http://pdr.bbaw.de/namespaces/aodl/", "timeDim"));
		// </timeDim>

		// <spatialDim>
		startElement = eventFactory.createStartElement("aodl", "http://pdr.bbaw.de/namespaces/aodl/", "spatialDim");
		eventWriter.add(startElement);
		//	<spatialStm>
		// same here: satisfy aodl schema by writing at least one spatialStm elements, (empty if none is available)
		// but not more than one dummy node
		SpatialDim spatialDim = a.getSpatialDim();
		Vector<SpatialStm> spatialStms = new Vector<SpatialStm>();
		if (spatialDim != null && spatialDim.getSpatialStms() != null)
			for (SpatialStm spatialStm : spatialDim.getSpatialStms())
				// TODO: does anything apart from this constitute a proper spatialStm?
				if (spatialStm.getPlaces() != null && !spatialStm.getPlaces().isEmpty())
					spatialStms.add(spatialStm);
		if (spatialStms.isEmpty()) {
			SpatialStm spatialStm = new SpatialStm();
			spatialStm.setType("undefined");
			spatialStms.add(spatialStm);
		}
		for (SpatialStm spatialStm : spatialStms)
			createSpatialStmNode(eventWriter, "spatialStm", spatialStm);
		eventWriter.add(eventFactory.createEndElement("aodl", "http://pdr.bbaw.de/namespaces/aodl/", "spatialDim"));
		// </spatialDim>


		// <relationDim>
		startElement = eventFactory.createStartElement("aodl", "http://pdr.bbaw.de/namespaces/aodl/", "relationDim");
		eventWriter.add(startElement);


		if (a.getRelationDim() != null && a.getRelationDim().getRelationStms() != null)
		{
			for (int i = 0; i < a.getRelationDim().getRelationStms().size(); i++)

			{

				createAspectRelationStmNode(eventWriter, "relationStm", a.getRelationDim().getRelationStms().get(i));
			}
		}
		eventWriter.add(eventFactory.createEndElement("aodl", "http://pdr.bbaw.de/namespaces/aodl/", "relationDim"));


		startElement = eventFactory.createStartElement("aodl", "http://pdr.bbaw.de/namespaces/aodl/", "semanticDim");
		eventWriter.add(startElement);


		if (a.getSemanticDim() != null && a.getSemanticDim().getSemanticStms() != null)
		{
			for (int i = 0; i < a.getSemanticDim().getSemanticStms().size(); i++)

			{

				if (a.getSemanticDim().getSemanticStms().get(i) != null)
				{
					createAspectSemanticStmNode(eventWriter, "semanticStm", a.getSemanticDim().getSemanticStms().get(i));
				}
			}
		}
		eventWriter.add(eventFactory.createEndElement("aodl", "http://pdr.bbaw.de/namespaces/aodl/", "semanticDim"));


		startElement = eventFactory.createStartElement("aodl", "http://pdr.bbaw.de/namespaces/aodl/", "notification");
		eventWriter.add(startElement);


		int start = 0;
		buflog(a.getNotification());
		
		// buflog("notifi " + a.getNotification());
		// FIXME!!!!!!!!!!!!!!!!
		if (a.getNotification() != null && a.getRangeList() != null)
		{
			// buflog("RangeListe hat TaggingListen, Zahl: " +
			// a.getRangeList().size());
			for (int i = 0; i < a.getRangeList().size(); i++)
			{
				if (a.getNotification().length() > start
						&& a.getNotification().length() >= a.getRangeList().get(i).getStart()
						&& start <= a.getRangeList().get(i).getStart())
				{
					String subText = a.getNotification().substring(start, a.getRangeList().get(i).getStart());
					processAppendTextWithLineBreaks(eventWriter, subText);

					createAspectMarkupNode(eventWriter, a.getRangeList().get(i), a.getNotification());
					start = a.getRangeList().get(i).getStart() + a.getRangeList().get(i).getLength();
				}
			}
			if (a.getNotification().length() > start)
			{
				String subText = a.getNotification().substring(start);
				processAppendTextWithLineBreaks(eventWriter, subText);

			}
		}
		else if (a.getNotification() != null)
		{
			processAppendTextWithLineBreaks(eventWriter, a.getNotification());

		}
		eventWriter.add(eventFactory.createEndElement("aodl", "http://pdr.bbaw.de/namespaces/aodl/", "notification"));


		startElement = eventFactory.createStartElement("aodl", "http://pdr.bbaw.de/namespaces/aodl/", "validation");
		eventWriter.add(startElement);


		if (a.getValidation() != null && a.getValidation().getValidationStms() != null)
		{
			for (int i = 0; i < a.getValidation().getValidationStms().size(); i++)
			{
				createValidationStmNode(eventWriter, "validationStm", a.getValidation().getValidationStms().get(i), "aodl",
						"http://pdr.bbaw.de/namespaces/aodl/", a);
			}
		}
		eventWriter.add(eventFactory.createEndElement("aodl", "http://pdr.bbaw.de/namespaces/aodl/", "validation"));


		eventWriter.add(eventFactory.createEndElement("aodl", "http://pdr.bbaw.de/namespaces/aodl/", "aspect"));

		eventWriter.add(eventFactory.createEndDocument());
		eventWriter.close();


		String xml = bout.toString();
		try {
			xml = bout.toString("UTF-8");
		} catch (UnsupportedEncodingException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

		if (logmsg.length()>0)
			log(IStatus.WARNING, logmsg, null);
		log(IStatus.INFO, "XMLProcessor output: " + xml, null);
		return xml;

	}

	/**
	 * Write to xml.
	 * @param object the object
	 * @return the string
	 * @throws XMLStreamException the xML stream exception
	 */
	public final String writeToXML(final PdrObject object) throws XMLStreamException
	{
		if (object instanceof Person)
		{
			return writeToXML((Person) object);
		}
		if (object instanceof Aspect)
		{
			return writeToXML((Aspect) object);
		}
		if (object instanceof ReferenceMods)
		{
			return writeToXML((ReferenceMods) object);
		}

		return null;
	}

	/**
	 * @param p person
	 * @return xml string
	 * @throws XMLStreamException xml Stream exc.
	 * @see org.bbaw.pdr.ae.control.core.XMLProcessorInterface#writeToXML(org.bbaw.pdr.ae.model.Person)
	 */
	@Override
	public final String writeToXML(final Person p) throws XMLStreamException
	{
		String logmsg = "";
		// Create a XMLOutputFactory
		XMLOutputFactory outputFactory = XMLOutputFactory.newInstance();
		// Create XMLEventWriter
		ByteArrayOutputStream bout = new ByteArrayOutputStream();

		XMLEventWriter eventWriter = outputFactory.createXMLEventWriter(bout, "UTF-8");

		// Create a EventFactory
		XMLEventFactory eventFactory = XMLEventFactory.newInstance();

		// Create and write Start Tag
		StartDocument startDocument = eventFactory.createStartDocument();
		eventWriter.add(startDocument);

		// Create config open tag
		StartElement startElement = eventFactory.createStartElement("podl", "http://pdr.bbaw.de/namespaces/podl/",
				"person");
		eventWriter.add(startElement);
		eventWriter.add(eventFactory.createNamespace("podl", "http://pdr.bbaw.de/namespaces/podl/"));
		eventWriter.add(eventFactory.createAttribute("xmlns:xsi", "http://www.w3.org/2001/XMLSchema-instance"));
		eventWriter.add(eventFactory.createAttribute("xsi:schemaLocation",
				"http://pdr.bbaw.de/namespaces/podl/ http://pdr.bbaw.de/schema/podl.xsd"));
		eventWriter.add(eventFactory.createAttribute("id", p.getPdrId().toString()));

		// add display name to the person node
		// eventWriter.add(eventFactory.createAttribute("displayName",
		// p.getDisplayName()));



		// Write the different nodes
		// TODO record is required. handle!
		if (p.getRecord() != null && p.getRecord().getRevisions() != null)
		{
			startElement = eventFactory.createStartElement("podl", "http://pdr.bbaw.de/namespaces/podl/", "record");
			eventWriter.add(startElement);


			for (int i = 0; i < p.getRecord().getRevisions().size(); i++)
			{

				createPDRObjectRelationNode(eventWriter, "revision", p.getRecord().getRevisions().get(i), "podl",
						"http://pdr.bbaw.de/namespaces/podl/");
			}
			eventWriter.add(eventFactory.createEndElement("podl", "http://pdr.bbaw.de/namespaces/podl/", "record"));

		}
		// identifiers must not be empty
		if (p.getIdentifiers() != null) {
			Vector<XMLEvent> idnsXmlEvs = new Vector<XMLEvent>();

			if (p.getIdentifiers().getIdentifiers() != null)
				for (Identifier i : p.getIdentifiers().getIdentifiers()){
					Vector<XMLEvent> idnXmlEvs = createPersonIdentifierNodes(eventWriter, "identifier", i);
					if (idnXmlEvs != null)
						idnsXmlEvs.addAll(idnXmlEvs);
				}
			
			if (!idnsXmlEvs.isEmpty()) {
				startElement = eventFactory.createStartElement("podl", "http://pdr.bbaw.de/namespaces/podl/", "identifiers");
				idnsXmlEvs.add(0, startElement);
				idnsXmlEvs.add(eventFactory.createEndElement("podl", "http://pdr.bbaw.de/namespaces/podl/", "identifiers"));
				for (XMLEvent e : idnsXmlEvs)
					eventWriter.add(e);
			}

		}

		if (p.getConcurrences() != null)
		{
			startElement = eventFactory.createStartElement("podl", "http://pdr.bbaw.de/namespaces/podl/",
					"concurrences");
			eventWriter.add(startElement);


			if (p.getConcurrences() != null && p.getConcurrences().getConcurrences() != null)
			{
				for (int i = 0; i < p.getConcurrences().getConcurrences().size(); i++)

				{

					createPersonConcurrenceNode(eventWriter, "concurrence", p.getConcurrences().getConcurrences().get(i), p);
				}
			}
			eventWriter.add(eventFactory
					.createEndElement("podl", "http://pdr.bbaw.de/namespaces/podl/", "concurrences"));

		}

		eventWriter.add(eventFactory.createEndElement("podl", "http://pdr.bbaw.de/namespaces/podl/", "person"));

		eventWriter.add(eventFactory.createEndDocument());
		eventWriter.close();


		String xml = bout.toString();
		try {
			xml = bout.toString("UTF-8");
		} catch (UnsupportedEncodingException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		log(IStatus.INFO, "XMLProcessor output: " + xml, null);
		return xml;

	}

	/**
	 * @param r Reference
	 * @return xml string
	 * @throws XMLStreamException exc
	 * @see org.bbaw.pdr.ae.control.core.XMLProcessorInterface#writeToXML(org.bbaw.pdr.ae.model.ReferenceMods)
	 */
	@Override
	public final String writeToXML(final ReferenceMods r) throws XMLStreamException
	{
		this.logmsg = "";
		// Create a XMLOutputFactory
		XMLOutputFactory outputFactory = XMLOutputFactory.newInstance();
		// Create XMLEventWriter

		ByteArrayOutputStream bout = new ByteArrayOutputStream();

		XMLEventWriter eventWriter = outputFactory.createXMLEventWriter(bout, "UTF-8");

		// Create a EventFactory
		XMLEventFactory eventFactory = XMLEventFactory.newInstance();

		// Create and write Start Tag
		StartDocument startDocument = eventFactory.createStartDocument();
		eventWriter.add(startDocument);

		// write mods node
		createModsNode(eventWriter, "mods", r, "mods", _modsUri);

		eventWriter.add(eventFactory.createEndDocument());
		eventWriter.close();



		String xml = bout.toString();
		try {
			xml = bout.toString("UTF-8");
		} catch (UnsupportedEncodingException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

		if (logmsg.length()>0)
			log(IStatus.WARNING, logmsg, null);
		log(IStatus.INFO, "XMLProcessor output: " + xml, null);
		return xml;

	}

	/**
	 * Write to xml.
	 * @param template the template
	 * @return the string
	 * @throws XMLStreamException the xML stream exception
	 */
	public String writeToXML(final ReferenceModsTemplate template) throws XMLStreamException
	{
		XMLOutputFactory outputFactory = XMLOutputFactory.newInstance();
		// Create XMLEventWriter

		ByteArrayOutputStream bout = new ByteArrayOutputStream();

		XMLEventWriter eventWriter = outputFactory.createXMLEventWriter(bout, "UTF-8");

		// Create a EventFactory
		XMLEventFactory eventFactory = XMLEventFactory.newInstance();

		// Create and write Start Tag
		StartDocument startDocument = eventFactory.createStartDocument();
		eventWriter.add(startDocument);

		// Create config open tag
		StartElement startElement = eventFactory.createStartElement("", "", "refTemplate");
		eventWriter.add(startElement);
		eventWriter.add(eventFactory.createAttribute("label", template.getLabel()));
		eventWriter.add(eventFactory.createAttribute("genre", template.getValue()));
		eventWriter.add(eventFactory.createAttribute("ignore", new Boolean(template.isIgnore()).toString()));

		startElement = eventFactory.createStartElement("", "", "usage");
		eventWriter.add(startElement);

		if (template.getImageString() != null)
		{
			startElement = eventFactory.createStartElement("", "", "image");
			eventWriter.add(startElement);

			Characters characters = eventFactory.createCharacters(template.getImageString());
			eventWriter.add(characters);

			eventWriter.add(eventFactory.createEndElement("", "", "image"));

		}
		if (template.getDocumentation() != null)
		{
			createModsTemplateDocumentationNode(eventWriter, "documentation", template.getDocumentation());
		}

		if (template.getRefTemplate() != null)
		{
			createModsNode(eventWriter, "mods", template.getRefTemplate(), "", "");
		}

		// Write the different nodes

		eventWriter.add(eventFactory.createEndElement("", "", "refTemplate"));


		eventWriter.add(eventFactory.createEndDocument());
		eventWriter.close();

		
		String xml = bout.toString();
		try {
			xml = bout.toString("UTF-8");
		} catch (UnsupportedEncodingException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

		log(IStatus.INFO, "XMLProcessor output: " + xml, null);
		return xml;

	}
}
