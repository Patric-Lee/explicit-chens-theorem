import PlattAssemblyKernel
import PlattCertificates.Count131072.C015984
import PlattCertificates.Count131072.C015985
import PlattCertificates.Count131072.C015986
import PlattCertificates.Count131072.C015987
import PlattCertificates.Count131072.C015988
import PlattCertificates.Count131072.C015989
import PlattCertificates.Count131072.C015990
import PlattCertificates.Count131072.C015991
import PlattCertificates.Count131072.C015992
import PlattCertificates.Count131072.C015993
import PlattCertificates.Count131072.C015994
import PlattCertificates.Count131072.C015995
import PlattCertificates.Count131072.C015996
import PlattCertificates.Count131072.C015997
import PlattCertificates.Count131072.C015998
import PlattCertificates.Count131072.C015999
import PlattCertificates.Count131072.C016000
import PlattCertificates.Count131072.C016001
import PlattCertificates.Count131072.C016002
import PlattCertificates.Count131072.C016003
import PlattCertificates.Count131072.C016004
import PlattCertificates.Count131072.C016005
import PlattCertificates.Count131072.C016006
import PlattCertificates.Count131072.C016007
import PlattCertificates.Count131072.C016008
import PlattCertificates.Count131072.C016009
import PlattCertificates.Count131072.C016010
import PlattCertificates.Count131072.C016011
import PlattCertificates.Count131072.C016012
import PlattCertificates.Count131072.C016013
import PlattCertificates.Count131072.C016014
import PlattCertificates.Count131072.C016015
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000187
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts15984 : List PrefixCut := [⟨1,6034514,6034518⟩,
⟨66,422409277,422409547⟩,
⟨128,818388877,818389403⟩]
theorem checked15984 : checkPrefixCuts (2^48) 2098987009 9 Manual.Count131072.C015984.packed 128 cuts15984 = true := by
 decide +kernel
def pointBounds15984 : List (Nat × Nat × Nat) := [(2098988032,97101628122110,97102006701626),(2099054592,97102044496873,97102423076655)]
theorem point_links_checked15984 : (cuts15984.take 2).map (fun c => (2098987009-1+2*2^9*c.k,97101622087596+c.lower,97102000667108+c.upper)) = pointBounds15984 := by
 decide +kernel
def cuts15985 : List PrefixCut := [⟨3,18906954,18906967⟩,
⟨68,431500813,431501088⟩,
⟨128,815387806,815388329⟩]
theorem checked15985 : checkPrefixCuts (2^48) 2099118081 9 Manual.Count131072.C015985.packed 128 cuts15985 = true := by
 decide +kernel
def pointBounds15985 : List (Nat × Nat × Nat) := [(2099121152,97102459383427,97102837963478),(2099187712,97102871977286,97103250557599)]
theorem point_links_checked15985 : (cuts15985.take 2).map (fun c => (2099118081-1+2*2^9*c.k,97102440476473+c.lower,97102819056511+c.upper)) = pointBounds15985 := by
 decide +kernel
def cuts15986 : List PrefixCut := [⟨5,32984526,32984546⟩,
⟨70,450781495,450781782⟩,
⟨128,823247786,823248314⟩]
theorem checked15986 : checkPrefixCuts (2^48) 2099249153 9 Manual.Count131072.C015986.packed 128 cuts15986 = true := by
 decide +kernel
def pointBounds15986 : List (Nat × Nat × Nat) := [(2099254272,97103288848805,97103667429386),(2099320832,97103706645774,97104085226622)]
theorem point_links_checked15986 : (cuts15986.take 2).map (fun c => (2099249153-1+2*2^9*c.k,97103255864279+c.lower,97103634444840+c.upper)) = pointBounds15986 := by
 decide +kernel
def cuts15987 : List PrefixCut := [⟨7,43976603,43976631⟩,
⟨72,460942626,460942920⟩,
⟨128,825207245,825207771⟩]
theorem checked15987 : checkPrefixCuts (2^48) 2099380225 9 Manual.Count131072.C015987.packed 128 cuts15987 = true := by
 decide +kernel
def pointBounds15987 : List (Nat × Nat × Nat) := [(2099387392,97104123088668,97104501669785),(2099453952,97104540054691,97104918636074)]
theorem point_links_checked15987 : (cuts15987.take 2).map (fun c => (2099380225-1+2*2^9*c.k,97104079112065+c.lower,97104457693154+c.upper)) = pointBounds15987 := by
 decide +kernel
def cuts15988 : List PrefixCut := [⟨9,56844221,56844257⟩,
⟨74,469895915,469896225⟩,
⟨128,813626401,813626930⟩]
theorem checked15988 : checkPrefixCuts (2^48) 2099511297 9 Manual.Count131072.C015988.packed 128 cuts15988 = true := by
 decide +kernel
def pointBounds15988 : List (Nat × Nat × Nat) := [(2099520512,97104961163531,97105339745182),(2099587072,97105374215225,97105752797150)]
theorem point_links_checked15988 : (cuts15988.take 2).map (fun c => (2099511297-1+2*2^9*c.k,97104904319310+c.lower,97105282900925+c.upper)) = pointBounds15988 := by
 decide +kernel
def cuts15989 : List PrefixCut := [⟨11,72525449,72525496⟩,
⟨76,485014603,485014915⟩,
⟨128,818669627,818670157⟩]
theorem checked15989 : checkPrefixCuts (2^48) 2099642369 9 Manual.Count131072.C015989.packed 128 cuts15989 = true := by
 decide +kernel
def pointBounds15989 : List (Nat × Nat × Nat) := [(2099653632,97105790471160,97106169053351),(2099720192,97106202960314,97106581542770)]
theorem point_links_checked15989 : (cuts15989.take 2).map (fun c => (2099642369-1+2*2^9*c.k,97105717945711+c.lower,97106096527855+c.upper)) = pointBounds15989 := by
 decide +kernel
def cuts15990 : List PrefixCut := [⟨13,82172463,82172512⟩,
⟨78,490614162,490614474⟩,
⟨128,814731062,814731584⟩]
theorem checked15990 : checkPrefixCuts (2^48) 2099773441 9 Manual.Count131072.C015990.packed 128 cuts15990 = true := by
 decide +kernel
def pointBounds15990 : List (Nat × Nat × Nat) := [(2099786752,97106618787801,97106997370524),(2099853312,97107027229500,97107405812486)]
theorem point_links_checked15990 : (cuts15990.take 2).map (fun c => (2099773441-1+2*2^9*c.k,97106536615338+c.lower,97106915198012+c.upper)) = pointBounds15990 := by
 decide +kernel
def cuts15991 : List PrefixCut := [⟨15,92756546,92756607⟩,
⟨80,501038260,501038588⟩,
⟨128,813741801,813742330⟩]
theorem checked15991 : checkPrefixCuts (2^48) 2099904513 9 Manual.Count131072.C015991.packed 128 cuts15991 = true := by
 decide +kernel
def pointBounds15991 : List (Nat × Nat × Nat) := [(2099919872,97107444102946,97107822686203),(2099986432,97107852384660,97108230968184)]
theorem point_links_checked15991 : (cuts15991.take 2).map (fun c => (2099904513-1+2*2^9*c.k,97107351346400+c.lower,97107729929596+c.upper)) = pointBounds15991 := by
 decide +kernel
def cuts15992 : List PrefixCut := [⟨17,107628364,107628432⟩,
⟨82,524864250,524864583⟩,
⟨128,820392745,820393268⟩]
theorem checked15992 : checkPrefixCuts (2^48) 2100035585 9 Manual.Count131072.C015992.packed 128 cuts15992 = true := by
 decide +kernel
def pointBounds15992 : List (Nat × Nat × Nat) := [(2100052992,97108272716565,97108651300358),(2100119552,97108689952451,97109068536509)]
theorem point_links_checked15992 : (cuts15992.take 2).map (fun c => (2100035585-1+2*2^9*c.k,97108165088201+c.lower,97108543671926+c.upper)) = pointBounds15992 := by
 decide +kernel
def cuts15993 : List PrefixCut := [⟨19,121560127,121560205⟩,
⟨84,537563396,537563740⟩,
⟨128,828784716,828785250⟩]
theorem checked15993 : checkPrefixCuts (2^48) 2100166657 9 Manual.Count131072.C015993.packed 128 cuts15993 = true := by
 decide +kernel
def pointBounds15993 : List (Nat × Nat × Nat) := [(2100186112,97109107041073,97109485625399),(2100252672,97109523044342,97109901628934)]
theorem point_links_checked15993 : (cuts15993.take 2).map (fun c => (2100166657-1+2*2^9*c.k,97108985480946+c.lower,97109364065194+c.upper)) = pointBounds15993 := by
 decide +kernel
def cuts15994 : List PrefixCut := [⟨21,139242574,139242663⟩,
⟨86,549858946,549859301⟩,
⟨128,817208292,817208820⟩]
theorem checked15994 : checkPrefixCuts (2^48) 2100297729 9 Manual.Count131072.C015994.packed 128 cuts15994 = true := by
 decide +kernel
def pointBounds15994 : List (Nat × Nat × Nat) := [(2100319232,97109953508236,97110332093107),(2100385792,97110364124608,97110742709745)]
theorem point_links_checked15994 : (cuts15994.take 2).map (fun c => (2100297729-1+2*2^9*c.k,97109814265662+c.lower,97110192850444+c.upper)) = pointBounds15994 := by
 decide +kernel
def cuts15995 : List PrefixCut := [⟨23,143120067,143120160⟩,
⟨88,556792413,556792770⟩,
⟨128,808446772,808447290⟩]
theorem checked15995 : checkPrefixCuts (2^48) 2100428801 9 Manual.Count131072.C015995.packed 128 cuts15995 = true := by
 decide +kernel
def pointBounds15995 : List (Nat × Nat × Nat) := [(2100452352,97110774594021,97111153179424),(2100518912,97111188266367,97111566852034)]
theorem point_links_checked15995 : (cuts15995.take 2).map (fun c => (2100428801-1+2*2^9*c.k,97110631473954+c.lower,97111010059264+c.upper)) = pointBounds15995 := by
 decide +kernel
def cuts15996 : List PrefixCut := [⟨25,160664949,160665051⟩,
⟨90,574445145,574445510⟩,
⟨128,821527874,821528396⟩]
theorem checked15996 : checkPrefixCuts (2^48) 2100559873 9 Manual.Count131072.C015996.packed 128 cuts15996 = true := by
 decide +kernel
def pointBounds15996 : List (Nat × Nat × Nat) := [(2100585472,97111600585675,97111979171605),(2100652032,97112014365871,97112392952064)]
theorem point_links_checked15996 : (cuts15996.take 2).map (fun c => (2100559873-1+2*2^9*c.k,97111439920726+c.lower,97111818506554+c.upper)) = pointBounds15996 := by
 decide +kernel
def cuts15997 : List PrefixCut := [⟨27,175661788,175661900⟩,
⟨92,595579205,595579587⟩,
⟨128,827104228,827104756⟩]
theorem checked15997 : checkPrefixCuts (2^48) 2100690945 9 Manual.Count131072.C015997.packed 128 cuts15997 = true := by
 decide +kernel
def pointBounds15997 : List (Nat × Nat × Nat) := [(2100718592,97112437110388,97112815696850),(2100785152,97112857027805,97113235614537)]
theorem point_links_checked15997 : (cuts15997.take 2).map (fun c => (2100690945-1+2*2^9*c.k,97112261448600+c.lower,97112640034950+c.upper)) = pointBounds15997 := by
 decide +kernel
def cuts15998 : List PrefixCut := [⟨29,183287743,183287864⟩,
⟨94,597819372,597819757⟩,
⟨128,816870075,816870601⟩]
theorem checked15998 : checkPrefixCuts (2^48) 2100822017 9 Manual.Count131072.C015998.packed 128 cuts15998 = true := by
 decide +kernel
def pointBounds15998 : List (Nat × Nat × Nat) := [(2100851712,97113271840571,97113650427570),(2100918272,97113686372200,97114064959463)]
theorem point_links_checked15998 : (cuts15998.take 2).map (fun c => (2100822017-1+2*2^9*c.k,97113088552828+c.lower,97113467139706+c.upper)) = pointBounds15998 := by
 decide +kernel
def cuts15999 : List PrefixCut := [⟨31,202970374,202970502⟩,
⟨96,622566665,622567062⟩,
⟨128,827001120,827001648⟩]
theorem checked15999 : checkPrefixCuts (2^48) 2100953089 9 Manual.Count131072.C015999.packed 128 cuts15999 = true := by
 decide +kernel
def pointBounds15999 : List (Nat × Nat × Nat) := [(2100984832,97114108393277,97114486980809),(2101051392,97114527989568,97114906577369)]
theorem point_links_checked15999 : (cuts15999.take 2).map (fun c => (2100953089-1+2*2^9*c.k,97113905422903+c.lower,97114284010307+c.upper)) = pointBounds15999 := by
 decide +kernel
def cuts16000 : List PrefixCut := [⟨33,215014504,215014640⟩,
⟨98,621589865,621590262⟩,
⟨128,813017442,813017964⟩]
theorem checked16000 : checkPrefixCuts (2^48) 2101084161 9 Manual.Count131072.C016000.packed 128 cuts16000 = true := by
 decide +kernel
def pointBounds16000 : List (Nat × Nat × Nat) := [(2101117952,97114947438527,97115326026595),(2101184512,97115354013888,97115732602217)]
theorem point_links_checked16000 : (cuts16000.take 2).map (fun c => (2101084161-1+2*2^9*c.k,97114732424023+c.lower,97115111011955+c.upper)) = pointBounds16000 := by
 decide +kernel
def cuts16001 : List PrefixCut := [⟨35,226521306,226521451⟩,
⟨100,639902518,639902928⟩,
⟨128,820066242,820066770⟩]
theorem checked16001 : checkPrefixCuts (2^48) 2101215233 9 Manual.Count131072.C016001.packed 128 cuts16001 = true := by
 decide +kernel
def pointBounds16001 : List (Nat × Nat × Nat) := [(2101251072,97115771962771,97116150551370),(2101317632,97116185343983,97116563932847)]
theorem point_links_checked16001 : (cuts16001.take 2).map (fun c => (2101215233-1+2*2^9*c.k,97115545441465+c.lower,97115924029919+c.upper)) = pointBounds16001 := by
 decide +kernel
def cuts16002 : List PrefixCut := [⟨37,237490835,237490985⟩,
⟨102,646961458,646961871⟩,
⟨128,812915939,812916456⟩]
theorem checked16002 : checkPrefixCuts (2^48) 2101346305 9 Manual.Count131072.C016002.packed 128 cuts16002 = true := by
 decide +kernel
def pointBounds16002 : List (Nat × Nat × Nat) := [(2101384192,97116602998542,97116981587674),(2101450752,97117012469165,97117391058560)]
theorem point_links_checked16002 : (cuts16002.take 2).map (fun c => (2101346305-1+2*2^9*c.k,97116365507707+c.lower,97116744096689+c.upper)) = pointBounds16002 := by
 decide +kernel
def cuts16003 : List PrefixCut := [⟨39,250735947,250736104⟩,
⟨104,663395133,663395556⟩,
⟨128,818222658,818223182⟩]
theorem checked16003 : checkPrefixCuts (2^48) 2101477377 9 Manual.Count131072.C016003.packed 128 cuts16003 = true := by
 decide +kernel
def pointBounds16003 : List (Nat × Nat × Nat) := [(2101517312,97117429159593,97117807749249),(2101583872,97117841818779,97118220408701)]
theorem point_links_checked16003 : (cuts16003.take 2).map (fun c => (2101477377-1+2*2^9*c.k,97117178423646+c.lower,97117557013145+c.upper)) = pointBounds16003 := by
 decide +kernel
def cuts16004 : List PrefixCut := [⟨41,268399198,268399370⟩,
⟨106,682907303,682907742⟩,
⟨128,823662946,823663474⟩]
theorem checked16004 : checkPrefixCuts (2^48) 2101608449 9 Manual.Count131072.C016004.packed 128 cuts16004 = true := by
 decide +kernel
def pointBounds16004 : List (Nat × Nat × Nat) := [(2101650432,97118265045502,97118643635697),(2101716992,97118679553607,97119058144069)]
theorem point_links_checked16004 : (cuts16004.take 2).map (fun c => (2101608449-1+2*2^9*c.k,97117996646304+c.lower,97118375236327+c.upper)) = pointBounds16004 := by
 decide +kernel
def cuts16005 : List PrefixCut := [⟨43,276819501,276819676⟩,
⟨108,693042345,693042790⟩,
⟨128,819460034,819460560⟩]
theorem checked16005 : checkPrefixCuts (2^48) 2101739521 9 Manual.Count131072.C016005.packed 128 cuts16005 = true := by
 decide +kernel
def pointBounds16005 : List (Nat × Nat × Nat) := [(2101783552,97119097128751,97119475719477),(2101850112,97119513351595,97119891942591)]
theorem point_links_checked16005 : (cuts16005.take 2).map (fun c => (2101739521-1+2*2^9*c.k,97118820309250+c.lower,97119198899801+c.upper)) = pointBounds16005 := by
 decide +kernel
def cuts16006 : List PrefixCut := [⟨45,288854442,288854624⟩,
⟨110,705318714,705319167⟩,
⟨128,823827845,823828374⟩]
theorem checked16006 : checkPrefixCuts (2^48) 2101870593 9 Manual.Count131072.C016006.packed 128 cuts16006 = true := by
 decide +kernel
def pointBounds16006 : List (Nat × Nat × Nat) := [(2101916672,97119928623726,97120307214985),(2101983232,97120345087998,97120723679528)]
theorem point_links_checked16006 : (cuts16006.take 2).map (fun c => (2101870593-1+2*2^9*c.k,97119639769284+c.lower,97120018360361+c.upper)) = pointBounds16006 := by
 decide +kernel
def cuts16007 : List PrefixCut := [⟨47,304503413,304503610⟩,
⟨112,720271695,720272164⟩,
⟨128,820830735,820831270⟩]
theorem checked16007 : checkPrefixCuts (2^48) 2102001665 9 Manual.Count131072.C016007.packed 128 cuts16007 = true := by
 decide +kernel
def pointBounds16007 : List (Nat × Nat × Nat) := [(2102049792,97120768100542,97121146692345),(2102116352,97121183868824,97121562460899)]
theorem point_links_checked16007 : (cuts16007.take 2).map (fun c => (2102001665-1+2*2^9*c.k,97120463597129+c.lower,97120842188735+c.upper)) = pointBounds16007 := by
 decide +kernel
def cuts16008 : List PrefixCut := [⟨49,310107975,310108180⟩,
⟨114,724243265,724243736⟩,
⟨128,814486314,814486840⟩]
theorem checked16008 : checkPrefixCuts (2^48) 2102132737 9 Manual.Count131072.C016008.packed 128 cuts16008 = true := by
 decide +kernel
def pointBounds16008 : List (Nat × Nat × Nat) := [(2102182912,97121594535839,97121973128185),(2102249472,97122008671129,97122387263741)]
theorem point_links_checked16008 : (cuts16008.take 2).map (fun c => (2102132737-1+2*2^9*c.k,97121284427864+c.lower,97121663020005+c.upper)) = pointBounds16008 := by
 decide +kernel
def cuts16009 : List PrefixCut := [⟨51,321335206,321335414⟩,
⟨116,743343472,743343955⟩,
⟨128,815506608,815507139⟩]
theorem checked16009 : checkPrefixCuts (2^48) 2102263809 9 Manual.Count131072.C016009.packed 128 cuts16009 = true := by
 decide +kernel
def pointBounds16009 : List (Nat × Nat × Nat) := [(2102316032,97122420249384,97122798842259),(2102382592,97122842257650,97123220850800)]
theorem point_links_checked16009 : (cuts16009.take 2).map (fun c => (2102263809-1+2*2^9*c.k,97122098914178+c.lower,97122477506845+c.upper)) = pointBounds16009 := by
 decide +kernel
def cuts16010 : List PrefixCut := [⟨53,340727821,340728039⟩,
⟨118,762843211,762843697⟩,
⟨128,823354690,823355215⟩]
theorem checked16010 : checkPrefixCuts (2^48) 2102394881 9 Manual.Count131072.C016010.packed 128 cuts16010 = true := by
 decide +kernel
def pointBounds16010 : List (Nat × Nat × Nat) := [(2102449152,97123255148607,97123633742023),(2102515712,97123677263997,97124055857681)]
theorem point_links_checked16010 : (cuts16010.take 2).map (fun c => (2102394881-1+2*2^9*c.k,97122914420786+c.lower,97123293013984+c.upper)) = pointBounds16010 := by
 decide +kernel
def cuts16011 : List PrefixCut := [⟨55,353825924,353826151⟩,
⟨120,772701753,772702246⟩,
⟨128,822366240,822366765⟩]
theorem checked16011 : checkPrefixCuts (2^48) 2102525953 9 Manual.Count131072.C016011.packed 128 cuts16011 = true := by
 decide +kernel
def pointBounds16011 : List (Nat × Nat × Nat) := [(2102582272,97124091601400,97124470195350),(2102648832,97124510477229,97124889071445)]
theorem point_links_checked16011 : (cuts16011.take 2).map (fun c => (2102525953-1+2*2^9*c.k,97123737775476+c.lower,97124116369199+c.upper)) = pointBounds16011 := by
 decide +kernel
def cuts16012 : List PrefixCut := [⟨57,368528789,368529028⟩,
⟨122,781622126,781622629⟩,
⟨128,818299256,818299783⟩]
theorem checked16012 : checkPrefixCuts (2^48) 2102657025 9 Manual.Count131072.C016012.packed 128 cuts16012 = true := by
 decide +kernel
def pointBounds16012 : List (Nat × Nat × Nat) := [(2102715392,97124928670505,97125307264992),(2102781952,97125341763842,97125720358593)]
theorem point_links_checked16012 : (cuts16012.take 2).map (fun c => (2102657025-1+2*2^9*c.k,97124560141716+c.lower,97124938735964+c.upper)) = pointBounds16012 := by
 decide +kernel
def cuts16013 : List PrefixCut := [⟨59,375599986,375600228⟩,
⟨124,791879598,791880109⟩,
⟨128,819184944,819185472⟩]
theorem checked16013 : checkPrefixCuts (2^48) 2102788097 9 Manual.Count131072.C016013.packed 128 cuts16013 = true := by
 decide +kernel
def pointBounds16013 : List (Nat × Nat × Nat) := [(2102848512,97125754040958,97126132635975),(2102915072,97126170320570,97126548915856)]
theorem point_links_checked16013 : (cuts16013.take 2).map (fun c => (2102788097-1+2*2^9*c.k,97125378440972+c.lower,97125757035747+c.upper)) = pointBounds16013 := by
 decide +kernel
def cuts16014 : List PrefixCut := [⟨61,395519700,395519961⟩,
⟨126,802002415,802002937⟩,
⟨128,813914293,813914823⟩]
theorem checked16014 : checkPrefixCuts (2^48) 2102919169 9 Manual.Count131072.C016014.packed 128 cuts16014 = true := by
 decide +kernel
def pointBounds16014 : List (Nat × Nat × Nat) := [(2102981632,97126593145616,97126971741180),(2103048192,97126999628331,97127378224156)]
theorem point_links_checked16014 : (cuts16014.take 2).map (fun c => (2102919169-1+2*2^9*c.k,97126197625916+c.lower,97126576221219+c.upper)) = pointBounds16014 := by
 decide +kernel
def cuts16015 : List PrefixCut := [⟨63,406737340,406737600⟩,
⟨128,814532775,814533293⟩]
theorem checked16015 : checkPrefixCuts (2^48) 2103050241 9 Manual.Count131072.C016015.packed 128 cuts16015 = true := by
 decide +kernel
def pointBounds16015 : List (Nat × Nat × Nat) := [(2103114752,97127418277549,97127796873642),(2103181312,97127826072984,97128204669335)]
theorem point_links_checked16015 : (cuts16015.take 2).map (fun c => (2103050241-1+2*2^9*c.k,97127011540209+c.lower,97127390136042+c.upper)) = pointBounds16015 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000187
