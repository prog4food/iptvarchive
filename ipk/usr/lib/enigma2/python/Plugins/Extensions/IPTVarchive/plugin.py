# -*- coding:utf-8 -*-
from . import _
import os, sys, time, re
try:
    import simplejson as json
except ImportError:
    import json
import tempfile, zlib, traceback, random

PY3 = (sys.version_info[0] == 3)
if PY3:
    from urllib.request import urlopen, Request
    from urllib.error import URLError
    from urllib.parse import urlparse, parse_qs, parse_qsl, urlencode, unquote, quote
else:
    from urllib import urlencode, unquote, quote
    from urllib2 import urlopen, Request, URLError
    from urlparse import urlparse, parse_qs, parse_qsl

from Plugins.Plugin import PluginDescriptor
from enigma import eServiceReference, eTimer
from ServiceReference import ServiceReference
from Screens.InfoBar import InfoBar
from Screens.InfoBarGenerics import InfoBarAudioSelection, InfoBarNotifications, InfoBarSubtitleSupport, InfoBarMenu
from Screens.MinuteInput import MinuteInput
from Screens.Screen import Screen
from Screens.EpgSelection import EPGSelection
from Screens.ChannelSelection import SimpleChannelSelection
from Screens.EventView import EventViewEPGSelect, EventViewBase
from Screens.MessageBox import MessageBox
from Components.Button import Button
from Components.ActionMap import ActionMap, HelpableActionMap
from Components.Sources.Boolean import Boolean
from Components.Sources.Event import Event
from Components.config import config
from Tools.HardwareInfo import HardwareInfo
from Tools.Directories import fileExists
try:
    import xml.etree.cElementTree as ET
except ImportError:
    import xml.etree.ElementTree as ET
from xml.sax.saxutils import unescape
from hashlib import md5
import _xxh32

xxh32 = _xxh32.xxh32()

try:
    from Plugins.Extensions.E2m3u2bouquet.e2m3u2bouquet import CFGPATH
except ImportError:
    CFGPATH = None

__author__ = 'alex1992, Vasiliks, Dorik1972, prog4food'
__version__ = '2.03'
__date__ = '2018-08-15'
__updated__ = '2020-11-22'
__foss_updated__ = '2023-04-20'

currTime = lambda: int(round(time.time()))
myStartTime = 0     # save last startTime
myDuration = 0      # save duration of played event
myTimeStamp = 0     # save timestamp of the last start
iptvHotKey = ''     # HotKey for Plugin
SIGN = chr(174) if PY3 else unichr(174).encode('utf-8')  # (R) symbol

paramExist = lambda fn, param: param in fn.__code__.co_varnames[:fn.__code__.co_argcount]

log_file = os.path.join(tempfile.gettempdir(), 'iptv_archive_plugin.log')

HEADERS = { 'User-Agent': 'Mozilla/5.0 (SmartHub; SMART-TV; U; Linux/SmartTV; Maple2012) AppleWebKit/534.7 (KHTML, like Gecko) SmartTV Safari/534.7',
            'Accept-encoding': 'gzip, deflate',
            'Connection': 'close',
           }
DEBUG = 0

def iptvLogWrite(str):
    with open(log_file, 'a') as f:
        f.write('%s\n' % str)

def getBoxInfo():
    res = {}.fromkeys(['model', 'distro', 'imagever'], 'unknown')
    for f in ['hwmodel', 'gbmodel', 'boxtype', 'vumodel', 'azmodel', 'model']:
        try:
            with open('/proc/stb/info/' + f, 'r') as f:
                res['model'] = ''.join(f.readlines()).strip()
                break
        except:
            continue
    try:
        with open('/etc/issue') as f:
            res['distro'], res['imagever'] = f.readlines()[-2].strip()[:-6].lower().split()
    except:
        pass
    return res

STATIC_INFO_DIC = getBoxInfo()

def query_get(query, key, default=''):
    '''
    Helper for getting values from a pre-parsed query string
    '''
    return parse_qs(query).get(key, [default])[0]

def xml_unescape(text):
    """
    This function transforms the "escaped" version suitable
    for well-formed XML formatting into humanly-readable string.

    Note that the default xml.sax.saxutils.unescape() function don't unescape
    some characters and we have to manually add them to the entities dictionary.

    :param text: The text that needs to be unescaped.
    :type text: str
    :rtype: str
    """
    text =  unescape(text, entities={r"&apos;": r"'", r"&quot;": r'"',
                                    r"&#124;": r"|",
                                    r"&#91;": r"[", r"&#93;": r"]", })

    return text if PY3 else text.encode('utf-8')

def getArchiveUrl(url, title=''):
    """
    This function converts the original url-link from userbouquet serviceref to an archive link

    :param url: original url-link
    :type url: str
    :rtype url: str (url-link to archive broadcast)
    """
    parsed_url = urlparse(url)
    splittedpath = parsed_url.path.split('/')
    token = query_get(parsed_url.query, 'token')
    if DEBUG:
        iptvLogWrite('Title: %s' % title)

    # cbilling
    if 'iptvx.tv' in url:
        if not 'video-timeshift' in splittedpath[-1]:
            if not token: token = splittedpath[2]
            if parsed_url.scheme == 'rtmp': #RTMP Enigma2 playlist
                parsed_url = parsed_url._replace(scheme='http')
            url = parsed_url._replace(netloc= '%s' % parsed_url.netloc.split(':')[0])._replace(query='token=%s' % token). \
                      _replace(path='%s/video-timeshift_abs-%d.m3u8' % (splittedpath[2] if 'static' in splittedpath else splittedpath[-1].split('.')[0] if 's' in splittedpath else splittedpath[1], myStartTime))
        else:
            url = parsed_url._replace(path='%s/video-timeshift_abs-%d.m3u8' % (splittedpath[1], myStartTime))
    # antifriz
    elif '.antifriz.' in url:
        if not token: token = splittedpath[2]
        if 'static' in splittedpath: #RTMP Enigma2 playlist
            splittedpath.append('video.m3u8')
            splittedpath.remove('static')
            parsed_url = parsed_url._replace(scheme='http')._replace(path='/'.join(splittedpath))

        url = parsed_url._replace(netloc='%s:80' % parsed_url.hostname)._replace(query='token=%s' % token). \
                          _replace(path='%s/archive-%d-%d.m3u8' % (splittedpath[-2], myStartTime, myDuration))
    # ZMediaProxy -  RT/Zabava/wink/zala
    elif any(x in url for x in ['/channel/', '/rmtv/', '/zatv/']):
        q = query_get(parsed_url.query, 'q')
        url = parsed_url._replace(query='q=%s&offset=%d&utcstart=%s' % (q, myStartTime-currTime(), myTimeStamp))
    # zala.by & zabava.tv
    elif any(x in url for x in ['.zala.', '178.124.183.', 'zabava', 'cdn.ngenix.net']):
        url = parsed_url._replace(query='version=2&offset=%d' % (myStartTime-currTime()))
    # 1ott
    elif '1ott.' in url:
        url = parsed_url._replace(query='archive=%d' % myStartTime)
    # tvoetv.in.ua
    elif any(x in url for x in['.onlineott.', '46.174.189']):
        login = query_get(parsed_url.query, 'login')
        key = query_get(parsed_url.query, 'key')
        if not '46.174.189.' in url:
            parsed_url = urlparse(unquote(query_get(parsed_url.query, 'url')))._replace(netloc='46.174.189.2:8091')
            splittedpath = parsed_url.path.split('/')

        url = parsed_url._replace(path='%s/archive-%d-%d.m3u8' % (splittedpath[1], myStartTime, myDuration)). \
                          _replace(query='login=%s&key=%s' % (login, key))
    # bcumedia
    elif any(x in url for x in ['.bcumedia.pro', '5.9.10.135']) and CFGPATH:
        if '.bcumedia.pro' in url:
            token = ''
            cfg_file = os.path.join(CFGPATH, 'config.xml')
            if fileExists(cfg_file):
                with open(cfg_file, 'r') as f:
                    token = re.findall(r"\[(https:\/\/bcumedia.pro.+?)\]", f.read())
            if token:
                token = os.path.splitext(os.path.basename(token[0]))[0]

            url = urlparse('http://5.9.10.135:8080/%s/video-%s-%s.m3u8?token=%s' % (md5(title.encode('utf-8')).hexdigest()[:9], myStartTime, myDuration, token))
        else:
            url = parsed_url._replace(path='%s/video-%s-%s.m3u8' % (splittedpath[1], myStartTime, myDuration))

    # itv.live & glanz & Other flussonic type with catchup-type="flussonic"
    elif any(x in url for x in ['.itv.', 'cdn.wf', '.ottg.']):
        url = parsed_url._replace(path='%s/index-%d-%d.m3u8' % (splittedpath[1], myStartTime, myDuration))
    # tv.team & 1cent & shura & ottclub & it999 & shara.club & fox-tv & Other with catchup="shift" or catchup="append"
    else:
        # tv.team
        if any(x in url for x in ['tv.team', 'troya.tv, 1usd.tv']) and 'static' in splittedpath: #RTMP Enigma2 playlist
                splittedpath.append('mono.m3u8')
                splittedpath.remove('static')
                parsed_url = parsed_url._replace(netloc='%s:24000' % parsed_url.netloc.split(':')[0])
                parsed_url = parsed_url._replace(scheme='http')._replace(path='/'.join(splittedpath))
        # 1cent
        if any(x in url for x in ['satbiling.com','only4.tv']) and not '82' in parsed_url.netloc:
            parsed_url = parsed_url._replace(netloc='%s:82' % parsed_url.netloc.split(':')[0])

        url = parsed_url._replace(query='token=%s&utc=%d&lutc=%d' % (token, myStartTime, myTimeStamp)) if token else parsed_url._replace(query='utc=%d&lutc=%d' % (myStartTime, myTimeStamp))

    if DEBUG:
        iptvLogWrite(url.geturl())

    return url.geturl()


class IPTVArchiveEventViewEPGSelect(EventViewEPGSelect):
    def __init__(self, session, event, ref, callback=None, singleEPGCB=None, multiEPGCB=None, similarEPGCB=None):
        Screen.__init__(self, session)
        self.skinName = ['iptvArchiveEventView', 'EventView']
        EventViewBase.__init__(self, event, ref, callback, similarEPGCB)
        self["key_red"] = Button('')
        self["key_green"] = Button('')
        self["key_yellow"] = Button('')
        self["key_blue"] = Button('')

        self["setupActions"] = ActionMap(["ColorActions"],
           {
               "cancel": self.cancel,
               "red": self.cancel,
               "green":self.cancel,
               "yellow": self.cancel,
            }, -2)

    def cancel(self):
        self.close(True)


class iptvArchiveSelection(EPGSelection):
    __module__ = __name__

    def __init__(self, session, service=None):
        if DEBUG:
            iptvLogWrite("\nIPTV Archive v%s :: Image: %s" % (__version__, STATIC_INFO_DIC['imagever']))

        if paramExist(EPGSelection.__init__, 'EPGtype'):
            EPGSelection.__init__(self, session, service, EPGtype='single')
        else:
            EPGSelection.__init__(self, session, service)
        self.service = service
        self.currentService = ServiceReference(service)
        self.oldService = self.session.nav.getCurrentlyPlayingServiceReference()
        self.noTMBD = _("The TMBD plugin is not installed!\nPlease install it.")
        self.skinName = ["iptvArchiveEPGSelection", "EPGSelection"]
        blueK = ''
        if STATIC_INFO_DIC['imagever'] != 'openpli': # No OpenPli !!!
            self["key_red"].setText('')
            self["key_yellow"].setText('')
            self["key_blue"].setText(_('Channel Selection'))
            blueK = "blue"

        self["key_red"].setText(_('TMBD Search'))
        self["key_green"].setText(_('Fake Events'))
        self["key_yellow"].setText(_('Gluing titles'))
        self["Service"].newService(self.service)

        self["setupActions"] = ActionMap(["ColorActions", "EPGSelectActions", "SetupActions"],
            {
               "cancel": self.cancel,
               "red": self.searchTMDB,
               "green":self.toggleFakeEvents,
               "yellow": self.toggleGlueTitles,
               "info": self.infoKeyPressed,
               blueK: self.blueButtonPressedNoPLi,
            }, -2)

        self.onClose.append(self.__onClose)

        global iptvHotKey
        for l in config.pickle().split('\n'):
            if 'Plugins/Extensions/IPTVarchive' in l:
                iptvHotKey = l.split('=')[0].split('.')[-1]
                break

        if DEBUG: iptvLogWrite('iptvHotKey: %s' % iptvHotKey)

    def __onClose(self):
        self.session.nav.playService(self.oldService)
        InfoBar.instance.doShow()

    def cancel(self):
        cs = self.session.nav.getCurrentlyPlayingServiceReference()
        self.showInfoBar() if cs and cs != self.oldService else self.close(True)

    def OK(self): # for OpenATV
        self.eventSelected()

    def searchTMDB(self):
       try:
            from Plugins.Extensions.TMBD.plugin import TMBD
            cs = self["list"].l.getCurrentSelection()
            if not (cs and cs[3]):
                return
            yr = [ _y for _y in re.findall(r'\d{4}', cs[0]) if '1930' <= _y <= '%s' % time.gmtime().tm_year ]
            self.session.open(TMBD, cs[4], yr[-1] if yr else None)
       except ImportError:
            self.session.open(MessageBox, self.noTMBD, type=MessageBox.TYPE_INFO, timeout=10)

    def eventSelected(self):
        global myStartTime
        global myDuration
        global myTimeStamp
        cs = self["list"].l.getCurrentSelection()
        if cs and cs[3]:              # duration != 0 ))
            myStartTime = cs[2]       # save startTime
            myDuration = cs[3]        # save duration
            myTimeStamp = currTime()  # get timestamp
            newRef = eServiceReference(str(self.currentService))
            newRef.setPath(getArchiveUrl(newRef.getPath(), self.currentService.getServiceName().replace('® ' if PY3 else u'® '.encode('utf-8'), '')))
            self.session.nav.playService(newRef)
            self.playedEvent = epgEvent(*cs)
            self.showInfoBar()

    def showInfoBar(self):
        self.hide()
        self.session.openWithCallback(lambda *args: self.close(True) if args else self.show(), iptvArchiveInfoBar, self.playedEvent)

    def onSelectionChanged(self):
        cs = self["list"].l.getCurrentSelection()
        if cs: self['Event'].newEvent(epgEvent(*cs))

    def infoKeyPressed(self):
        cs = self["list"].l.getCurrentSelection()
        if cs: self.session.open(IPTVArchiveEventViewEPGSelect, epgEvent(*cs), self.currentService)

    def setService(self, service):
        self.currentService = service
        self.service = eServiceReference(str(service))
        self.onCreate()

    def channelSelectionCallback(self, *args):
        if args:
            try:
                serviceref, bouquetref = args[:2]
                self.parent = self
                self.parent.epg_bouquet = bouquetref
            except:
                serviceref = args[0]
            finally:
                self.setService(ServiceReference(serviceref))

    def blueButtonPressedNoPLi(self):
        if paramExist(SimpleChannelSelection.__init__, 'currentBouquet'):
            self.session.openWithCallback(self.channelSelectionCallback, SimpleChannelSelection, _("Channel Selection"), currentBouquet=True,)
        else:
            self.session.openWithCallback(self.channelSelectionCallback, SimpleChannelSelection, _("Channel Selection"))

    def toggleFakeEvents(self):
        if self["key_green"].getText() == _('Fake Events'):
            self["key_red"].setText("")
            self["key_green"].setText('EPG')
            self["key_yellow"].setText('')
            self.fakeArchiveListLoaded()
        else:
            self["key_red"].setText(_('TMBD Search'))
            self["key_green"].setText(_('Fake Events'))
            self["key_yellow"].setText(_('Gluing titles'))
            self.onCreate()

    def toggleGlueTitles(self):
        if self["key_yellow"].getText() == _('Gluing titles'):
            self["key_green"].setText('')
            self["key_yellow"].setText('EPG')
            self.GlueTitle()
        else:
            self["key_yellow"].setText(_('Gluing titles'))
            self["key_green"].setText(_('Fake Events'))
            self.onCreate()

    def addEvent(self, event):
        """ Event = [descr, eventid, btime, duration, title]
                      str     int     int     int      str
        """
        if not self.provider:
            return

        if self.provider in ('shura', '1ott'):
            return (xml_unescape(event.findtext('text')), int(event.attrib.get('id')), int(event.findtext('start_time')),
                      int(event.findtext('duration')), xml_unescape(event.findtext('name')))

        elif self.provider == 'itv':
            btime = int(event.get('startTime'))
            duration = int(event.get('stopTime')) - btime
            if btime < currTime():
                return (xml_unescape(event.get('desc')), random.randint(0, 1000), btime, duration, xml_unescape(event.get('title')))
        else:
            btime = int(event.get('time'))
            duration = int(event.get('time_to')) - btime
            if currTime() - self.days * 86400 < btime < currTime(): # 86400 - SECONDS_PER_DAY
                return (xml_unescape(event.get('descr')), random.randint(0, 1000), btime, duration, xml_unescape(event.get('name')))

    def GlueTitle(self):
        self["list"].recalcEntrySize()
        if self.provider is None:
            self.list1item(_("No access to archive"), _("Not IPTV Channel. No access to archive") if not self.currentService.getPath() else _("Unknown IPTV provider. No access to archive"))
            return

        li = self["list"].list
        l = self["list"]
        l.list = []

        pattern = re.compile(r'(х|Х|м|М|x|X|т|Т|T)/(Ф|ф|С|C|с|c)|«|»|"', re.DOTALL)
        conv = lambda text: pattern.sub('', text).strip()

        for x in sorted(li, key=lambda x: [int(c) if c.isdigit() else c for c in re.split(r'(\d+)', conv(x[4]))]):
            li = list(x)
            li[4] = conv(li[4])
            x = tuple(li)
            if not any(x[4] in li for li in l.list):
                l.list.append(x)

        l.l.setList(l.list)
        l.selectionChanged()

    def fakeArchiveListLoaded(self):
        self["list"].recalcEntrySize()
        if self.provider is None:
            self.list1item(_("No access to archive"), _("Not IPTV Channel. No access to archive") if not self.currentService.getPath() else _("Unknown IPTV provider. No access to archive"))
            return

        l = self["list"]
        l.list = []
        li = self["list"].list
        start = (currTime()/3600)*3600
        while (start > currTime() - (self.days * 24 * 3600)):
            li.append((_('Fake EPG'), random.randint(0, 1000), int(start), 3600, time.strftime("%A, %d.%m, %H:%M",time.localtime(start))))
            start -= 3600
        l.l.setList(l.list)
        l.selectionChanged()

    def archiveListLoaded(self, raw):
        try:
            if PY3: raw = raw.decode('utf-8')
            events = {'shura': lambda: ET.fromstring(raw).findall('event'),
                      '1ott' : lambda: ET.fromstring(raw).findall('event'),
                      'itv'  : lambda: json.loads(raw).get('res', '' or 'None'),
                      }.get(self.provider, lambda: json.loads(raw).get('epg_data', '' or 'None') if 'epg_data' in raw else json.loads(raw or 'null'))()

            if events:
                l = self["list"]
                l.list = sorted([_f for _f in map(self.addEvent, events) if _f], key=lambda x: x[2], reverse=True)
                if l.list:
                    l.l.setList(l.list)
                    l.selectionChanged()
                else:
                    self.list1item(_("No archive"), _("There are no archive entries for this channel satisfying the conditions of a given search depth"))
            else:
                self.list1item(_("No archive"), _("There are no archive entries for this channel"))
        except:
            self.list1item(_("No archive"), _("EPG data parsing error"))
            if DEBUG: self.saveTraceback()

    def onCreate(self, firstrun=False):
        try:
            self["list"].recalcEntrySize()
            if STATIC_INFO_DIC['imagever'] == 'openbh' and not HardwareInfo().is_nextgen():  # OpenBH !!!
                self.createTimer.stop()
            service = self.currentService
            chName = service.getServiceName().replace(SIGN, '')
            url = service.getPath()
            self["Service"].newService(service.ref)
            self.setTitle(_("IPTV Archive") + ' - ' + chName)

            if not url: # DVB
                self.list1item(_("No access to archive"), _("Not IPTV Channel. No access to archive"))
                self.provider, self.days = None, 0
                return
            parsed_url = urlparse(url)
            params = dict(parse_qsl(parsed_url.fragment))
            splittedpath = parsed_url.path.split('/')
            providers = {
                          'tvshka.net'  : ('shura', 7),      # shura.tv
                          '1ott.'       : ('1ott', 8),       # my.1ott.net
                          'only4.tv'    : ('only4', 7),      # 1cent.tv
                          'satbiling.com': ('iptvx.one', 7), # iptv.satbilling.com
                          '.crd-s.'     : ('iptvx.one', 3),  # crdru.net
                          '/live/s.'    : ('shara.club', 2), # shara.club
                          '/live/u.'    : ('ipstream', 3),   # ipstream.one
                          '/iptv/'      : ('it999', 3),      # it999.tv (ilook.tv)
                          '.ottg.'      : ('iptvx.one', 7),  # glanz (ottg.tv)
                          '.fox-tv.'    : ('fox-tv', 5),     # fox-tv.fun
                          '.iptv.'      : ('online', 1),     # iptv.online
                          '.mymagic.'   : ('magic', 7),      # mymagic.tv
                          'tvfor.pro'   : ('shara-tv', 5),   # shara-tv.org
                          'uz-tv'       : ('uz-tv', 5),      # uz-tv.net
                          '.bcumedia.pro': ('bcu', 2),       # bcumedia.pro
                          '.antifriz.'  : ('antifriz', 7),   # antifriz.tx
                          'app-greatiptv': ('app-greatiptv', 7),     # app.greatiptv.cc
                          '.zala.'      : ('zala', 2),       # zala.by
                          '/zatv/'      : ('zala', 2),       # ZMedia Proxy local zala.by
                          '178.124.183.': ('zala', 2),       # zala.by
                          'zabava'      : ('zabava', 3),     # zabava.tv
                          'cdn.ngenix.net': ('zabava', 3),   # zabava.tv
                          '.spr24.'     : ('sharavoz', 3),   # sharavoz.tv
                          '.onlineott.' : ('tvoetv', 5),     # tvoetv.in.ua
                          '85.143.191.' : ('ttv', 5),        # ttv.run
                          'myott.top'   : ('ottclub', 5),    # ottclub.cc
                          '.itv.'       : ('itv', 3),        # itv.live
                          'cdn.wf'      : ('itv', 3),        # itv.live
                          'iptvx.tv'    : ('cbilling', 7),   # cbilling.me
                          'tv.team'     : ('tvteam', 7),     # tv.team
                          'troya.tv'    : ('tvteam', 7),     # tv.team
                          '1usd.tv'     : ('tvteam', 7),     # tv.team
                          'cdntv.online': ('viplime', 3),    # viplime.fun
                          '.tvdosug.'   : ('propg.net', 1),  # tvdosug.tv
                          '/channel/'   : ('zmedia', 3),     # ZMedia Proxy vps https://t.me/wink_news/107
                          '/rmtv/'      : ('iptvx.one', 7),  # ZMedia Proxy local
                          'undefined'   : (None, 0),
                         }
            # Provider name, Depth of archive in days
            self.provider, self.days = providers[next(iter([x for x in list(providers.keys()) if x in url]), 'undefined')]
            if 'sapp_catchup-days' in params:
                self.days = int(params['sapp_catchup-days'])
                if self.provider is None:
                    self.provider = 'flussonic'

            if self.provider is None:
                self.list1item(_("No access to archive"), _("Unknown IPTV provider. No access to archive"))
                return
            # shura & 1ott Native API
            elif self.provider in ('shura', '1ott'):
                epgUrl = Request(parsed_url._replace(path='/'.join(splittedpath[:3]) + '/epg/archive.xml').geturl(), headers=HEADERS)
            # ottclub Native API
            elif self.provider == 'ottclub':
                epgUrl = Request('http://spacetv.in/api/channel/%s' % splittedpath[-1].split('.')[0], headers=HEADERS)
            # itv.live Native API
            elif self.provider == 'itv':
                data = urlencode({ 'action': 'epg',
                                   'chid'  : splittedpath[-2],
                                   'name'  : chName,
                                   'token' : query_get(parsed_url.query, 'token'),
                                   'serv'  : parsed_url.netloc.split(':')[0],
                                 }).encode('utf-8')
                epgUrl = Request('http://api.itv.live/epg.php', data, HEADERS)
            # cbilling Native API
            elif self.provider == 'cbilling':
                epgUrl = Request('http://%s/epg/%s?date=' % ('api.' + '.'.join(parsed_url.hostname.split('.')[1:]),
                                  splittedpath[2] if 'static' in splittedpath else splittedpath[1] if 'token' in parsed_url.query else splittedpath[-1].split('.')[0]), headers=HEADERS) 
            # tv.team Native API
            elif self.provider == 'tvteam':
                epgUrl = Request('http://tv.team/%s.json' % (splittedpath[-2] if not 'static' in splittedpath else splittedpath[-1]), headers=HEADERS)
            # For e2m3u2b compatibility with shara.club & ipstream used Native API
            elif self.provider in ('shara.club', 'ipstream') and 'sapp_tvgid' in params:
                data = urlencode({'type': 'epg',
                                  'ch'  : params['sapp_tvgid'], }).encode('utf-8')
                epgUrl = Request('%s://%s/get/' % (parsed_url.scheme, 'api.' + '.'.join(parsed_url.hostname.split('.')[1:])), data, HEADERS)
            # For e2m3u2b compatibility with OTT-play FOSS EPG
            elif self.provider in ('it999', 'app-greatiptv', 'iptvx.one', 'only4', 'bcu', 'propg.net'
                                  # нет поддержки
                                  # 'fox-tv', 'antifriz', 'magic', 'uz-tv', 'shara-tv', 'viplime'
                                  ) and 'sapp_tvgid' in params:
                xxh32.__init__(data=params['sapp_tvgid'])
                epgUrl = Request('http://epg.ottp.eu.org/%s/epg/%s.json' % (self.provider, xxh32.intdigest()), headers=HEADERS)
            # The rest for compatibility if we do not use e2m3u2b and there is no tvg-id.
            # We are looking for by name in EPG in OTT-play by Alex
            else:
                # TODO: Адаптировать
                # epgUrl = Request('http://epg.ott-play.com/m3u/ge2.php', urlencode({'channel': chName}).encode('utf-8'), HEADERS)
                pass
            try:
                resp = urlopen(epgUrl, timeout=5)
                if DEBUG:
                    iptvLogWrite(self.provider + " ch: " + chName + '\nepgUrl: ' + resp.geturl())

                self.archiveListLoaded( {'deflate': lambda: zlib.decompress(resp.read(), -zlib.MAX_WBITS),
                                         'gzip'   : lambda: zlib.decompress(resp.read(), zlib.MAX_WBITS|16),
                                         }.get(resp.info().get('Content-Encoding'), lambda: resp.read())()
                                       )
            except URLError as e:
                self.list1item(_("Error getting archive"), _("Can't download the EPG data.\nFailed to reach a server or the API server couldn't fulfill the request"))
                if DEBUG:
                    iptvLogWrite(self.provider + ' ch: %s\n APIurl: %s\n Error: %s' % (chName, epgUrl.get_full_url(), e.reason if hasattr(e, 'reason') else e.code))

            finally:
                try:
                    resp.close()
                except NameError:
                    pass
        except:
            self.list1item(_("Error getting archive"), _("Error generating request URL for receiving EPG archive broadcasts"))
            if DEBUG: self.saveTraceback()

    def list1item(self, title='', descr=''):
        btime = currTime()
        self["list"].list = []
        self["list"].l.setList(self["list"].list)
        self['Event'].newEvent(epgEvent(descr, random.randint(0, 1000), btime, 0, title))
        self["list"].selectionChanged()

    def saveTraceback(self):
        with open(log_file, 'a') as err_file:
            traceback.print_exc(file=err_file)


class epgEvent(object):
    def __init__(self, descr, eventid, btime, duration, title):
        """
        Set broadcast EPG info for current selection
        0 -> short description
        1 -> eventid
        2 -> begin time
        3 -> duration time
        4 -> title
        """
        self.descr = descr if descr is not '' else _("Description not available")
        self.eventid = eventid if eventid else random.randint(0, 1000)
        self.btime = btime
        self.duration = duration
        self.title = title

    def getEventName(self): return self.title
    def getShortDescription(self): return self.descr
    def getExtendedDescription(self): return ''
    def getBeginTime(self): return self.btime
    def getDuration(self): return self.duration
    def getBeginTimeString(self): return time.strftime("%d.%m, %H:%M", time.localtime(self.btime))
    def getEventId(self): return self.eventid
    def getGenreData(self): return None
    def getParentalData(self): return None
    def getGenreDataList(self): return None
    def getPdcPil(self): return 0
    def getRunningStatus(self): return 4
    def getArchiveBeginTimeString(self):
        return _('Archive for') + time.strftime(' {%w}, %d %B %Y', time.localtime(self.btime)).format(*[ _('sunday'),
                                                                                                         _('monday'),
                                                                                                         _('tuesday'),
                                                                                                         _('wednesday'),
                                                                                                         _('thursday'),
                                                                                                         _('friday'),
                                                                                                         _('saturday'),
                                                                                                       ])


class iptvArchiveSecondInfoBar(Screen):
    def __init__(self, session):
        Screen.__init__(self, session)
        self.skinName = ['iptvArchiveSecondInfoBar', 'SecondInfoBar']
        self["OkCancelActions"] = HelpableActionMap(self, "OkCancelActions",
            {
                "ok": self.close,
                "cancel": self.close,
            }, -2)

class iptvArchiveInfoBar(Screen, InfoBarAudioSelection, InfoBarNotifications, InfoBarSubtitleSupport, InfoBarMenu):
    STATE_HIDDEN = 0
    STATE_SHOWN = 1

    def __init__(self, session, ev):
        Screen.__init__(self, session)
        for x in InfoBarAudioSelection, InfoBarNotifications, InfoBarSubtitleSupport, InfoBarMenu:
            x.__init__(self)
        self.skinName = ['iptvArchiveInfoBar', 'InfoBar']
        self.skinAttributes = None
        self.session.screen['Event_Now'] = Event()
        self.session.screen['Event_Next'] = Event()
        self.strRef = str(ServiceReference(self.session.nav.getCurrentlyPlayingServiceReference()))
        self.ev = ev
        self.hideTimer = eTimer()
        try: # For DreamOS
            self.timer_conn = self.hideTimer.timeout.connect(self.doTimerHide)
        except:
            self.hideTimer.callback.append(self.doTimerHide)

        self["setupActions"] = ActionMap([ "MediaPlayerActions", "HotkeyActions", "InfobarSeekActions", "SetupActions",],
            {
                "ok": self.ok,
                "cancel": self.cancel,
                "info": self.close,
                "epg": self.close,
                iptvHotKey: self.close,
                "pause": self.pause,
                "play": self.pause,
                "stop": self.stop,
                "1": lambda: self.myjump(1),
                "3": lambda: self.myjump(3),
                "4": lambda: self.myjump(4),
                "6": lambda: self.myjump(6),
                "7": lambda: self.myjump(7),
                "9": lambda: self.myjump(9),
                "seekBack": lambda: self.myjump(7),
                "seekFwd": lambda: self.myjump(9),
            }, -2)

        # BH image reqirements
        self["HbbtvApplication"] = Boolean(fixed=0)
        self["HbbtvApplication"].name = ""
        # VTI image reqirements
        self["KeyRedText"] = Boolean(fixed=0)
        self["KeyRedText"].name = ""
        self["KeyGreenText"] = Boolean(fixed=0)
        self["KeyGreenText"].name = ""
        self["KeyYellowText"] = Boolean(fixed=0)
        self["KeyYellowText"].name = ""
        self["KeyBlueText"] = Boolean(fixed=0)
        self["KeyBlueText"].name = ""
        # end VTI
        self.onClose.append(self.__onClose)
        self.updateEvent()
        self.doShow()

    def __onClose(self):
        global myStartTime
        global myTimeStamp
        myStartTime = myStartTime + currTime() - myTimeStamp
        myTimeStamp = currTime()

    def ok(self):
        global myTimeStamp
        if myTimeStamp > 0: # not paused
            if self.__state == self.STATE_SHOWN:
                self.__state = self.STATE_HIDDEN
                self.hide()
                self.session.open(iptvArchiveSecondInfoBar)
            else:
                self.doShow()
        else:
            self.myjump(0)

    def doShow(self):
        self.__state = self.STATE_SHOWN
        self.show()
        self.startHideTimer()

    def doTimerHide(self):
        self.hideTimer.stop()
        self.__state = self.STATE_HIDDEN
        self.hide()

    def startHideTimer(self):
        if self.__state == self.STATE_SHOWN:
            idx = config.usage.infobar_timeout.index
            if idx:
                self.hideTimer.start(idx * 1000, True)

    def pause(self):
        global myTimeStamp
        if myTimeStamp > 0: # not paused
            self.session.nav.stopService()
            global myStartTime
            myStartTime = myStartTime + currTime() - myTimeStamp  # calculate new archive startTime
            myTimeStamp = 0
            self.doShow()
        else:
            self.myjump(0)

    def stop(self, value=True):
        if value:
            self.close(True)

    def cancel(self):
        if paramExist(MessageBox.__init__, 'title'):
            self.session.openWithCallback(self.stop, MessageBox, _("%s\n\nStop playback and exit plugin?") %  self.ev.getEventName(),
                                                                      timeout=10, default=True, title=self.strRef.split(':')[-1])
        else:
            self.session.openWithCallback(self.stop, MessageBox, _("%s\n\nStop playback and exit plugin?") %  self.ev.getEventName(),
                                                                      timeout=10, default=True)

    def updateEvent(self):
        ev = self.ev
        btime = ev.getBeginTime()
        self.session.screen['Event_Now'].newEvent(epgEvent(ev.getShortDescription(), random.randint(0, 1000), currTime() + btime - myStartTime, ev.getDuration(), ev.getEventName()))
        self.session.screen['Event_Next'].newEvent(epgEvent('', random.randint(0, 1000), btime, ev.getDuration(), ev.getArchiveBeginTimeString()))

    def myjump(self, secondsJump=0):
        global myStartTime
        global myTimeStamp
        secondsJump = { 0: 0,
                        1: -config.seek.selfdefined_13.value,
                        3: config.seek.selfdefined_13.value,
                        4: -config.seek.selfdefined_46.value,
                        6: config.seek.selfdefined_46.value,
                        7: -config.seek.selfdefined_79.value,
                        9: config.seek.selfdefined_79.value
                      }.get(secondsJump, secondsJump)

        if myTimeStamp > 0:
            startTime = myStartTime + currTime() - myTimeStamp + secondsJump  # calculate new archive startTime
        else:
            startTime = myStartTime + secondsJump  # calculate new archive startTime if paused
        if currTime() > startTime:    # if not startTime in future
            myStartTime = startTime   # save new startTime
            myTimeStamp = currTime()  # save new timestamp
            newRef = eServiceReference(self.strRef)
            newRef.setPath(getArchiveUrl(newRef.getPath()))
            self.session.nav.playService(newRef)  # start new service event
            self.updateEvent()
            self.doShow()


def where_extensionsmenu(session, **kwargs):
    session.open(iptvArchiveSelection, session.nav.getCurrentlyPlayingServiceReference())

def Plugins(**kwargs):
    return [
             PluginDescriptor( name = _("IPTV Archive"),
                               description = _("View the archive of IPTV broadcasts"),
                               where = [PluginDescriptor.WHERE_EXTENSIONSMENU, PluginDescriptor.WHERE_PLUGINMENU],
                               fnc = where_extensionsmenu,
                               icon="iptvarchive.png",
                               needsRestart = False)
            ]

