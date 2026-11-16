import PlattAssemblyKernel
import PlattCertificates.Count131072.C021984
import PlattCertificates.Count131072.C021985
import PlattCertificates.Count131072.C021986
import PlattCertificates.Count131072.C021987
import PlattCertificates.Count131072.C021988
import PlattCertificates.Count131072.C021989
import PlattCertificates.Count131072.C021990
import PlattCertificates.Count131072.C021991
import PlattCertificates.Count131072.C021992
import PlattCertificates.Count131072.C021993
import PlattCertificates.Count131072.C021994
import PlattCertificates.Count131072.C021995
import PlattCertificates.Count131072.C021996
import PlattCertificates.Count131072.C021997
import PlattCertificates.Count131072.C021998
import PlattCertificates.Count131072.C021999
import PlattCertificates.Count131072.C022000
import PlattCertificates.Count131072.C022001
import PlattCertificates.Count131072.C022002
import PlattCertificates.Count131072.C022003
import PlattCertificates.Count131072.C022004
import PlattCertificates.Count131072.C022005
import PlattCertificates.Count131072.C022006
import PlattCertificates.Count131072.C022007
import PlattCertificates.Count131072.C022008
import PlattCertificates.Count131072.C022009
import PlattCertificates.Count131072.C022010
import PlattCertificates.Count131072.C022011
import PlattCertificates.Count131072.C022012
import PlattCertificates.Count131072.C022013
import PlattCertificates.Count131072.C022014
import PlattCertificates.Count131072.C022015
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000062
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts21984 : List PrefixCut := [⟨46,210903108,210903219⟩,
⟨128,596119290,596119623⟩]
theorem checked21984 : checkPrefixCuts (2^48) 2885419009 9 Manual.Count131072.C021984.packed 128 cuts21984 = true := by
 decide +kernel
def pointBounds21984 : List (Nat × Nat × Nat) := [(2885466112,101244103820074,101244484899096)]
theorem point_links_checked21984 : (cuts21984.take 1).map (fun c => (2885419009-1+2*2^9*c.k,101243892916966+c.lower,101244273995877+c.upper)) = pointBounds21984 := by
 decide +kernel
def cuts21985 : List PrefixCut := [⟨7,34726460,34726478⟩,
⟨96,444998959,444999210⟩,
⟨128,592385652,592385986⟩]
theorem checked21985 : checkPrefixCuts (2^48) 2885550081 9 Manual.Count131072.C021985.packed 128 cuts21985 = true := by
 decide +kernel
def pointBounds21985 : List (Nat × Nat × Nat) := [(2885557248,101244523762716,101244904841978),(2885648384,101244934035215,101245315114710)]
theorem point_links_checked21985 : (cuts21985.take 2).map (fun c => (2885550081-1+2*2^9*c.k,101244489036256+c.lower,101244870115500+c.upper)) = pointBounds21985 := by
 decide +kernel
def cuts21986 : List PrefixCut := [⟨57,261702366,261702514⟩,
⟨128,587286623,587286956⟩]
theorem checked21986 : checkPrefixCuts (2^48) 2885681153 9 Manual.Count131072.C021986.packed 128 cuts21986 = true := by
 decide +kernel
def pointBounds21986 : List (Nat × Nat × Nat) := [(2885739520,101245343124274,101245724204000)]
theorem point_links_checked21986 : (cuts21986.take 1).map (fun c => (2885681153-1+2*2^9*c.k,101245081421908+c.lower,101245462501486+c.upper)) = pointBounds21986 := by
 decide +kernel
def cuts21987 : List PrefixCut := [⟨18,82809068,82809117⟩,
⟨107,490019052,490019339⟩,
⟨128,587942615,587942958⟩]
theorem checked21987 : checkPrefixCuts (2^48) 2885812225 9 Manual.Count131072.C021987.packed 128 cuts21987 = true := by
 decide +kernel
def pointBounds21987 : List (Nat × Nat × Nat) := [(2885830656,101245751517599,101246132597559),(2885921792,101246158727583,101246539807781)]
theorem point_links_checked21987 : (cuts21987.take 2).map (fun c => (2885812225-1+2*2^9*c.k,101245668708531+c.lower,101246049788442+c.upper)) = pointBounds21987 := by
 decide +kernel
def cuts21988 : List PrefixCut := [⟨68,310541551,310541729⟩,
⟨128,586160383,586160721⟩]
theorem checked21988 : checkPrefixCuts (2^48) 2885943297 9 Manual.Count131072.C021988.packed 128 cuts21988 = true := by
 decide +kernel
def pointBounds21988 : List (Nat × Nat × Nat) := [(2886012928,101246567192697,101246948273129)]
theorem point_links_checked21988 : (cuts21988.take 1).map (fun c => (2885943297-1+2*2^9*c.k,101246256651146+c.lower,101246637731400+c.upper)) = pointBounds21988 := by
 decide +kernel
def cuts21989 : List PrefixCut := [⟨29,133320967,133321041⟩,
⟨118,539322065,539322381⟩,
⟨128,586718914,586719260⟩]
theorem checked21989 : checkPrefixCuts (2^48) 2886074369 9 Manual.Count131072.C021989.packed 128 cuts21989 = true := by
 decide +kernel
def pointBounds21989 : List (Nat × Nat × Nat) := [(2886104064,101246976132496,101247357213162),(2886195200,101247382133594,101247763214502)]
theorem point_links_checked21989 : (cuts21989.take 2).map (fun c => (2886074369-1+2*2^9*c.k,101246842811529+c.lower,101247223892121+c.upper)) = pointBounds21989 := by
 decide +kernel
def cuts21990 : List PrefixCut := [⟨79,362687394,362687608⟩,
⟨128,584546814,584547158⟩]
theorem checked21990 : checkPrefixCuts (2^48) 2886205441 9 Manual.Count131072.C021990.packed 128 cuts21990 = true := by
 decide +kernel
def pointBounds21990 : List (Nat × Nat × Nat) := [(2886286336,101247792217837,101248173298989)]
theorem point_links_checked21990 : (cuts21990.take 1).map (fun c => (2886205441-1+2*2^9*c.k,101247429530443+c.lower,101247810611381+c.upper)) = pointBounds21990 := by
 decide +kernel
def cuts21991 : List PrefixCut := [⟨40,178264904,178265004⟩,
⟨128,581204650,581204975⟩]
theorem checked21991 : checkPrefixCuts (2^48) 2886336513 9 Manual.Count131072.C021991.packed 128 cuts21991 = true := by
 decide +kernel
def pointBounds21991 : List (Nat × Nat × Nat) := [(2886377472,101248192342161,101248573423543)]
theorem point_links_checked21991 : (cuts21991.take 1).map (fun c => (2886336513-1+2*2^9*c.k,101248014077257+c.lower,101248395158539+c.upper)) = pointBounds21991 := by
 decide +kernel
def cuts21992 : List PrefixCut := [⟨1,4680736,4680739⟩,
⟨90,411898267,411898500⟩,
⟨128,587809179,587809507⟩]
theorem checked21992 : checkPrefixCuts (2^48) 2886467585 9 Manual.Count131072.C021992.packed 128 cuts21992 = true := by
 decide +kernel
def pointBounds21992 : List (Nat × Nat × Nat) := [(2886468608,101248599962643,101248981044253),(2886559744,101249007180174,101249388262014)]
theorem point_links_checked21992 : (cuts21992.take 2).map (fun c => (2886467585-1+2*2^9*c.k,101248595281907+c.lower,101248976363514+c.upper)) = pointBounds21992 := by
 decide +kernel
def cuts21993 : List PrefixCut := [⟨51,232366411,232366541⟩,
⟨128,592267780,592268112⟩]
theorem checked21993 : checkPrefixCuts (2^48) 2886598657 9 Manual.Count131072.C021993.packed 128 cuts21993 = true := by
 decide +kernel
def pointBounds21993 : List (Nat × Nat × Nat) := [(2886650880,101249415457497,101249796539562)]
theorem point_links_checked21993 : (cuts21993.take 1).map (fun c => (2886598657-1+2*2^9*c.k,101249183091086+c.lower,101249564173021+c.upper)) = pointBounds21993 := by
 decide +kernel
def cuts21994 : List PrefixCut := [⟨12,56163620,56163653⟩,
⟨101,460807537,460807794⟩,
⟨128,585708270,585708597⟩]
theorem checked21994 : checkPrefixCuts (2^48) 2886729729 9 Manual.Count131072.C021994.packed 128 cuts21994 = true := by
 decide +kernel
def pointBounds21994 : List (Nat × Nat × Nat) := [(2886742016,101249831522486,101250212604786),(2886833152,101250236166403,101250617248927)]
theorem point_links_checked21994 : (cuts21994.take 2).map (fun c => (2886729729-1+2*2^9*c.k,101249775358866+c.lower,101250156441133+c.upper)) = pointBounds21994 := by
 decide +kernel
def cuts21995 : List PrefixCut := [⟨62,280315362,280315526⟩,
⟨128,586461527,586461862⟩]
theorem checked21995 : checkPrefixCuts (2^48) 2886860801 9 Manual.Count131072.C021995.packed 128 cuts21995 = true := by
 decide +kernel
def pointBounds21995 : List (Nat × Nat × Nat) := [(2886924288,101250641382498,101251022465256)]
theorem point_links_checked21995 : (cuts21995.take 1).map (fun c => (2886860801-1+2*2^9*c.k,101250361067136+c.lower,101250742149730+c.upper)) = pointBounds21995 := by
 decide +kernel
def cuts21996 : List PrefixCut := [⟨23,108221954,108222014⟩,
⟨112,515459866,515460170⟩,
⟨128,588872464,588872812⟩]
theorem checked21996 : checkPrefixCuts (2^48) 2886991873 9 Manual.Count131072.C021996.packed 128 cuts21996 = true := by
 decide +kernel
def pointBounds21996 : List (Nat × Nat × Nat) := [(2887015424,101251055750617,101251436833606),(2887106560,101251462988529,101251844071762)]
theorem point_links_checked21996 : (cuts21996.take 2).map (fun c => (2886991873-1+2*2^9*c.k,101250947528663+c.lower,101251328611592+c.upper)) = pointBounds21996 := by
 decide +kernel
def cuts21997 : List PrefixCut := [⟨73,332350086,332350274⟩,
⟨128,581338882,581339215⟩]
theorem checked21997 : checkPrefixCuts (2^48) 2887122945 9 Manual.Count131072.C021997.packed 128 cuts21997 = true := by
 decide +kernel
def pointBounds21997 : List (Nat × Nat × Nat) := [(2887197696,101251868751213,101252249834678)]
theorem point_links_checked21997 : (cuts21997.take 1).map (fun c => (2887122945-1+2*2^9*c.k,101251536401127+c.lower,101251917484404+c.upper)) = pointBounds21997 := by
 decide +kernel
def cuts21998 : List PrefixCut := [⟨34,158418344,158418431⟩,
⟨123,558891142,558891460⟩,
⟨128,581410050,581410381⟩]
theorem checked21998 : checkPrefixCuts (2^48) 2887254017 9 Manual.Count131072.C021998.packed 128 cuts21998 = true := by
 decide +kernel
def pointBounds21998 : List (Nat × Nat × Nat) := [(2887288832,101252276158353,101252657242050),(2887379968,101252676631151,101253057715079)]
theorem point_links_checked21998 : (cuts21998.take 2).map (fun c => (2887254017-1+2*2^9*c.k,101252117740009+c.lower,101252498823619+c.upper)) = pointBounds21998 := by
 decide +kernel
def cuts21999 : List PrefixCut := [⟨84,386129858,386130080⟩,
⟨128,585770343,585770678⟩]
theorem checked21999 : checkPrefixCuts (2^48) 2887385089 9 Manual.Count131072.C021999.packed 128 cuts21999 = true := by
 decide +kernel
def pointBounds21999 : List (Nat × Nat × Nat) := [(2887471104,101253085279917,101253466364080)]
theorem point_links_checked21999 : (cuts21999.take 1).map (fun c => (2887385089-1+2*2^9*c.k,101252699150059+c.lower,101253080234000+c.upper)) = pointBounds21999 := by
 decide +kernel
def cuts22000 : List PrefixCut := [⟨45,211334830,211334945⟩,
⟨128,586816041,586816362⟩]
theorem checked22000 : checkPrefixCuts (2^48) 2887516161 9 Manual.Count131072.C022000.packed 128 cuts22000 = true := by
 decide +kernel
def pointBounds22000 : List (Nat × Nat × Nat) := [(2887562240,101253496255232,101253877339623)]
theorem point_links_checked22000 : (cuts22000.take 1).map (fun c => (2887516161-1+2*2^9*c.k,101253284920402+c.lower,101253666004678+c.upper)) = pointBounds22000 := by
 decide +kernel
def cuts22001 : List PrefixCut := [⟨6,27877968,27877983⟩,
⟨95,435805715,435805966⟩,
⟨128,586496901,586497240⟩]
theorem checked22001 : checkPrefixCuts (2^48) 2887647233 9 Manual.Count131072.C022001.packed 128 cuts22001 = true := by
 decide +kernel
def pointBounds22001 : List (Nat × Nat × Nat) := [(2887653376,101253899614411,101254280699023),(2887744512,101254307542158,101254688627006)]
theorem point_links_checked22001 : (cuts22001.take 2).map (fun c => (2887647233-1+2*2^9*c.k,101253871736443+c.lower,101254252821040+c.upper)) = pointBounds22001 := by
 decide +kernel
def cuts22002 : List PrefixCut := [⟨56,250790627,250790768⟩,
⟨128,583448593,583448923⟩]
theorem checked22002 : checkPrefixCuts (2^48) 2887778305 9 Manual.Count131072.C022002.packed 128 cuts22002 = true := by
 decide +kernel
def pointBounds22002 : List (Nat × Nat × Nat) := [(2887835648,101254709023971,101255090109048)]
theorem point_links_checked22002 : (cuts22002.take 1).map (fun c => (2887778305-1+2*2^9*c.k,101254458233344+c.lower,101254839318280+c.upper)) = pointBounds22002 := by
 decide +kernel
def cuts22003 : List PrefixCut := [⟨17,78752825,78752867⟩,
⟨106,484790105,484790385⟩,
⟨128,587613172,587613512⟩]
theorem checked22003 : checkPrefixCuts (2^48) 2887909377 9 Manual.Count131072.C022003.packed 128 cuts22003 = true := by
 decide +kernel
def pointBounds22003 : List (Nat × Nat × Nat) := [(2887926784,101255120434762,101255501520070),(2888017920,101255526472042,101255907557588)]
theorem point_links_checked22003 : (cuts22003.take 2).map (fun c => (2887909377-1+2*2^9*c.k,101255041681937+c.lower,101255422767203+c.upper)) = pointBounds22003 := by
 decide +kernel
def cuts22004 : List PrefixCut := [⟨67,304176087,304176262⟩,
⟨128,581933856,581934187⟩]
theorem checked22004 : checkPrefixCuts (2^48) 2888040449 9 Manual.Count131072.C022004.packed 128 cuts22004 = true := by
 decide +kernel
def pointBounds22004 : List (Nat × Nat × Nat) := [(2888109056,101255933471196,101256314556977)]
theorem point_links_checked22004 : (cuts22004.take 1).map (fun c => (2888040449-1+2*2^9*c.k,101255629295109+c.lower,101256010380715+c.upper)) = pointBounds22004 := by
 decide +kernel
def cuts22005 : List PrefixCut := [⟨28,127961486,127961560⟩,
⟨117,532693371,532693678⟩,
⟨128,581517618,581517954⟩]
theorem checked22005 : checkPrefixCuts (2^48) 2888171521 9 Manual.Count131072.C022005.packed 128 cuts22005 = true := by
 decide +kernel
def pointBounds22005 : List (Nat × Nat × Nat) := [(2888200192,101256339190451,101256720276462),(2888291328,101256743922336,101257125008580)]
theorem point_links_checked22005 : (cuts22005.take 2).map (fun c => (2888171521-1+2*2^9*c.k,101256211228965+c.lower,101256592314902+c.upper)) = pointBounds22005 := by
 decide +kernel
def cuts22006 : List PrefixCut := [⟨78,360182803,360183014⟩,
⟨128,587435816,587436160⟩]
theorem checked22006 : checkPrefixCuts (2^48) 2888302593 9 Manual.Count131072.C022006.packed 128 cuts22006 = true := by
 decide +kernel
def pointBounds22006 : List (Nat × Nat × Nat) := [(2888382464,101257152929386,101257534015870)]
theorem point_links_checked22006 : (cuts22006.take 1).map (fun c => (2888302593-1+2*2^9*c.k,101256792746583+c.lower,101257173832856+c.upper)) = pointBounds22006 := by
 decide +kernel
def cuts22007 : List PrefixCut := [⟨39,178525303,178525406⟩,
⟨128,590040127,590040468⟩]
theorem checked22007 : checkPrefixCuts (2^48) 2888433665 9 Manual.Count131072.C022007.packed 128 cuts22007 = true := by
 decide +kernel
def pointBounds22007 : List (Nat × Nat × Nat) := [(2888473600,101257558707702,101257939794422),(2888564736,101257970222526,101258351309484)]
theorem point_links_checked22007 : (cuts22007.take 2).map (fun c => (2888433665-1+2*2^9*c.k,101257380182399+c.lower,101257761269016+c.upper)) = pointBounds22007 := by
 decide +kernel
def cuts22008 : List PrefixCut := [⟨89,406045047,406045282⟩,
⟨128,581828247,581828585⟩]
theorem checked22008 : checkPrefixCuts (2^48) 2888564737 9 Manual.Count131072.C022008.packed 128 cuts22008 = true := by
 decide +kernel
def pointBounds22008 : List (Nat × Nat × Nat) := [(2888655872,101258376267573,101258757354766)]
theorem point_links_checked22008 : (cuts22008.take 1).map (fun c => (2888564737-1+2*2^9*c.k,101257970222526+c.lower,101258351309484+c.upper)) = pointBounds22008 := by
 decide +kernel
def cuts22009 : List PrefixCut := [⟨50,228689955,228690088⟩,
⟨128,585796796,585797126⟩]
theorem checked22009 : checkPrefixCuts (2^48) 2888695809 9 Manual.Count131072.C022009.packed 128 cuts22009 = true := by
 decide +kernel
def pointBounds22009 : List (Nat × Nat × Nat) := [(2888747008,101258780740728,101259161828157)]
theorem point_links_checked22009 : (cuts22009.take 1).map (fun c => (2888695809-1+2*2^9*c.k,101258552050773+c.lower,101258933138069+c.upper)) = pointBounds22009 := by
 decide +kernel
def cuts22010 : List PrefixCut := [⟨11,47743408,47743432⟩,
⟨100,453067996,453068247⟩,
⟨128,584211180,584211505⟩]
theorem checked22010 : checkPrefixCuts (2^48) 2888826881 9 Manual.Count131072.C022010.packed 128 cuts22010 = true := by
 decide +kernel
def pointBounds22010 : List (Nat × Nat × Nat) := [(2888838144,101259185590977,101259566678627),(2888929280,101259590915565,101259972003442)]
theorem point_links_checked22010 : (cuts22010.take 2).map (fun c => (2888826881-1+2*2^9*c.k,101259137847569+c.lower,101259518935195+c.upper)) = pointBounds22010 := by
 decide +kernel
def cuts22011 : List PrefixCut := [⟨61,280014530,280014690⟩,
⟨128,588374209,588374545⟩]
theorem checked22011 : checkPrefixCuts (2^48) 2888957953 9 Manual.Count131072.C022011.packed 128 cuts22011 = true := by
 decide +kernel
def pointBounds22011 : List (Nat × Nat × Nat) := [(2889020416,101260002073279,101260383161390)]
theorem point_links_checked22011 : (cuts22011.take 1).map (fun c => (2888957953-1+2*2^9*c.k,101259722058749+c.lower,101260103146700+c.upper)) = pointBounds22011 := by
 decide +kernel
def cuts22012 : List PrefixCut := [⟨22,101420978,101421031⟩,
⟨111,514696051,514696336⟩,
⟨128,590101255,590101584⟩]
theorem checked22012 : checkPrefixCuts (2^48) 2889089025 9 Manual.Count131072.C022012.packed 128 cuts22012 = true := by
 decide +kernel
def pointBounds22012 : List (Nat × Nat × Nat) := [(2889111552,101260411853936,101260792942276),(2889202688,101260825129009,101261206217581)]
theorem point_links_checked22012 : (cuts22012.take 2).map (fun c => (2889089025-1+2*2^9*c.k,101260310432958+c.lower,101260691521245+c.upper)) = pointBounds22012 := by
 decide +kernel
def cuts22013 : List PrefixCut := [⟨72,335031509,335031694⟩,
⟨128,591730605,591730937⟩]
theorem checked22013 : checkPrefixCuts (2^48) 2889220097 9 Manual.Count131072.C022013.packed 128 cuts22013 = true := by
 decide +kernel
def pointBounds22013 : List (Nat × Nat × Nat) := [(2889293824,101261235565722,101261616654523)]
theorem point_links_checked22013 : (cuts22013.take 1).map (fun c => (2889220097-1+2*2^9*c.k,101260900534213+c.lower,101261281622829+c.upper)) = pointBounds22013 := by
 decide +kernel
def cuts22014 : List PrefixCut := [⟨33,154893758,154893846⟩,
⟨122,560628633,560628952⟩,
⟨128,587417404,587417740⟩]
theorem checked22014 : checkPrefixCuts (2^48) 2889351169 9 Manual.Count131072.C022014.packed 128 cuts22014 = true := by
 decide +kernel
def pointBounds22014 : List (Nat × Nat × Nat) := [(2889384960,101261647158576,101262028247612),(2889476096,101262052893451,101262433982718)]
theorem point_links_checked22014 : (cuts22014.take 2).map (fun c => (2889351169-1+2*2^9*c.k,101261492264818+c.lower,101261873353766+c.upper)) = pointBounds22014 := by
 decide +kernel
def cuts22015 : List PrefixCut := [⟨83,375816177,375816392⟩,
⟨128,579597823,579598157⟩]
theorem checked22015 : checkPrefixCuts (2^48) 2889482241 9 Manual.Count131072.C022015.packed 128 cuts22015 = true := by
 decide +kernel
def pointBounds22015 : List (Nat × Nat × Nat) := [(2889567232,101262455498399,101262836587898)]
theorem point_links_checked22015 : (cuts22015.take 1).map (fun c => (2889482241-1+2*2^9*c.k,101262079682222+c.lower,101262460771506+c.upper)) = pointBounds22015 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000062
