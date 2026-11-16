import PlattAssemblyKernel
import PlattCertificates.Count131072.C012976
import PlattCertificates.Count131072.C012977
import PlattCertificates.Count131072.C012978
import PlattCertificates.Count131072.C012979
import PlattCertificates.Count131072.C012980
import PlattCertificates.Count131072.C012981
import PlattCertificates.Count131072.C012982
import PlattCertificates.Count131072.C012983
import PlattCertificates.Count131072.C012984
import PlattCertificates.Count131072.C012985
import PlattCertificates.Count131072.C012986
import PlattCertificates.Count131072.C012987
import PlattCertificates.Count131072.C012988
import PlattCertificates.Count131072.C012989
import PlattCertificates.Count131072.C012990
import PlattCertificates.Count131072.C012991
import PlattCertificates.Count131072.C012992
import PlattCertificates.Count131072.C012993
import PlattCertificates.Count131072.C012994
import PlattCertificates.Count131072.C012995
import PlattCertificates.Count131072.C012996
import PlattCertificates.Count131072.C012997
import PlattCertificates.Count131072.C012998
import PlattCertificates.Count131072.C012999
import PlattCertificates.Count131072.C013000
import PlattCertificates.Count131072.C013001
import PlattCertificates.Count131072.C013002
import PlattCertificates.Count131072.C013003
import PlattCertificates.Count131072.C013004
import PlattCertificates.Count131072.C013005
import PlattCertificates.Count131072.C013006
import PlattCertificates.Count131072.C013007
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000093
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts12976 : List PrefixCut := [⟨20,147281490,147281597⟩,
⟨73,573926260,573926677⟩,
⟨126,994613604,994614321⟩,
⟨128,1009968107,1009968835⟩]
theorem checked12976 : checkPrefixCuts (2^48) 1704722433 9 Manual.Count131072.C012976.packed 128 cuts12976 = true := by
 decide +kernel
def pointBounds12976 : List (Nat × Nat × Nat) := [(1704742912,94360247071329,94360623778652),(1704797184,94360673716099,94361050423732),(1704851456,94361094403443,94361471111376)]
theorem point_links_checked12976 : (cuts12976.take 3).map (fun c => (1704722433-1+2*2^9*c.k,94360099789839+c.lower,94360476497055+c.upper)) = pointBounds12976 := by
 decide +kernel
def cuts12977 : List PrefixCut := [⟨51,406970379,406970676⟩,
⟨104,834234692,834235300⟩,
⟨128,1020787051,1020787794⟩]
theorem checked12977 : checkPrefixCuts (2^48) 1704853505 9 Manual.Count131072.C012977.packed 128 cuts12977 = true := by
 decide +kernel
def pointBounds12977 : List (Nat × Nat × Nat) := [(1704905728,94361516728325,94361893436566),(1704960000,94361943992638,94362320701190)]
theorem point_links_checked12977 : (cuts12977.take 2).map (fun c => (1704853505-1+2*2^9*c.k,94361109757946+c.lower,94361486465890+c.upper)) = pointBounds12977 := by
 decide +kernel
def cuts12978 : List PrefixCut := [⟨29,231783508,231783674⟩,
⟨82,652747352,652747825⟩,
⟨128,1016911650,1016912389⟩]
theorem checked12978 : checkPrefixCuts (2^48) 1704984577 9 Manual.Count131072.C012978.packed 128 cuts12978 = true := by
 decide +kernel
def pointBounds12978 : List (Nat × Nat × Nat) := [(1705014272,94362362328505,94362739037358),(1705068544,94362783292349,94363160001509)]
theorem point_links_checked12978 : (cuts12978.take 2).map (fun c => (1704984577-1+2*2^9*c.k,94362130544997+c.lower,94362507253684+c.upper)) = pointBounds12978 := by
 decide +kernel
def cuts12979 : List PrefixCut := [⟨7,56291040,56291082⟩,
⟨60,473266372,473266717⟩,
⟨113,907230585,907231247⟩,
⟨128,1030038760,1030039508⟩]
theorem checked12979 : checkPrefixCuts (2^48) 1705115649 9 Manual.Count131072.C012979.packed 128 cuts12979 = true := by
 decide +kernel
def pointBounds12979 : List (Nat × Nat × Nat) := [(1705122816,94363203747687,94363580457155),(1705177088,94363620723019,94363997432790),(1705231360,94364054687232,94364431397320)]
theorem point_links_checked12979 : (cuts12979.take 3).map (fun c => (1705115649-1+2*2^9*c.k,94363147456647+c.lower,94363524166073+c.upper)) = pointBounds12979 := by
 decide +kernel
def cuts12980 : List PrefixCut := [⟨38,304044404,304044627⟩,
⟨91,727417175,727417706⟩,
⟨128,1025833325,1025834070⟩]
theorem checked12980 : checkPrefixCuts (2^48) 1705246721 9 Manual.Count131072.C012980.packed 128 cuts12980 = true := by
 decide +kernel
def pointBounds12980 : List (Nat × Nat × Nat) := [(1705285632,94364481539811,94364858250208),(1705339904,94364904912582,94365281623287)]
theorem point_links_checked12980 : (cuts12980.take 2).map (fun c => (1705246721-1+2*2^9*c.k,94364177495407+c.lower,94364554205581+c.upper)) = pointBounds12980 := by
 decide +kernel
def cuts12981 : List PrefixCut := [⟨16,119166501,119166591⟩,
⟨69,533104693,533105082⟩,
⟨122,950000450,950001141⟩,
⟨128,996706472,996707197⟩]
theorem checked12981 : checkPrefixCuts (2^48) 1705377793 9 Manual.Count131072.C012981.packed 128 cuts12981 = true := by
 decide +kernel
def pointBounds12981 : List (Nat × Nat × Nat) := [(1705394176,94365322495233,94365699206242),(1705448448,94365736433425,94366113144733),(1705502720,94366153329182,94366530040792)]
theorem point_links_checked12981 : (cuts12981.take 3).map (fun c => (1705377793-1+2*2^9*c.k,94365203328732+c.lower,94365580039651+c.upper)) = pointBounds12981 := by
 decide +kernel
def cuts12982 : List PrefixCut := [⟨47,382224048,382224326⟩,
⟨100,800413538,800414116⟩,
⟨128,1023860547,1023861288⟩]
theorem checked12982 : checkPrefixCuts (2^48) 1705508865 9 Manual.Count131072.C012982.packed 128 cuts12982 = true := by
 decide +kernel
def pointBounds12982 : List (Nat × Nat × Nat) := [(1705556992,94366582259252,94366958971174),(1705611264,94367000448742,94367377160964)]
theorem point_links_checked12982 : (cuts12982.take 2).map (fun c => (1705508865-1+2*2^9*c.k,94366200035204+c.lower,94366576746848+c.upper)) = pointBounds12982 := by
 decide +kernel
def cuts12983 : List PrefixCut := [⟨25,206280910,206281058⟩,
⟨78,630549541,630549998⟩,
⟨128,1035333211,1035333961⟩]
theorem checked12983 : checkPrefixCuts (2^48) 1705639937 9 Manual.Count131072.C012983.packed 128 cuts12983 = true := by
 decide +kernel
def pointBounds12983 : List (Nat × Nat × Nat) := [(1705665536,94367430176661,94367806889194),(1705719808,94367854445292,94368231158134)]
theorem point_links_checked12983 : (cuts12983.take 2).map (fun c => (1705639937-1+2*2^9*c.k,94367223895751+c.lower,94367600608136+c.upper)) = pointBounds12983 := by
 decide +kernel
def cuts12984 : List PrefixCut := [⟨3,24256931,24256949⟩,
⟨56,440578134,440578459⟩,
⟨109,864476310,864476947⟩,
⟨128,1017102752,1017103495⟩]
theorem checked12984 : checkPrefixCuts (2^48) 1705771009 9 Manual.Count131072.C012984.packed 128 cuts12984 = true := by
 decide +kernel
def pointBounds12984 : List (Nat × Nat × Nat) := [(1705774080,94368283485893,94368660199046),(1705828352,94368699807096,94369076520556),(1705882624,94369123705272,94369500419044)]
theorem point_links_checked12984 : (cuts12984.take 3).map (fun c => (1705771009-1+2*2^9*c.k,94368259228962+c.lower,94368635942097+c.upper)) = pointBounds12984 := by
 decide +kernel
def cuts12985 : List PrefixCut := [⟨34,271258237,271258431⟩,
⟨87,691499448,691499952⟩,
⟨128,1011414953,1011415685⟩]
theorem checked12985 : checkPrefixCuts (2^48) 1705902081 9 Manual.Count131072.C012985.packed 128 cuts12985 = true := by
 decide +kernel
def pointBounds12985 : List (Nat × Nat × Nat) := [(1705936896,94369547589951,94369924304023),(1705991168,94369967831162,94370344545544)]
theorem point_links_checked12985 : (cuts12985.take 2).map (fun c => (1705902081-1+2*2^9*c.k,94369276331714+c.lower,94369653045592+c.upper)) = pointBounds12985 := by
 decide +kernel
def cuts12986 : List PrefixCut := [⟨12,94207760,94207828⟩,
⟨65,515412269,515412644⟩,
⟨118,936933231,936933917⟩,
⟨128,1020081011,1020081756⟩]
theorem checked12986 : checkPrefixCuts (2^48) 1706033153 9 Manual.Count131072.C012986.packed 128 cuts12986 = true := by
 decide +kernel
def pointBounds12986 : List (Nat × Nat × Nat) := [(1706045440,94370381954427,94370758669105),(1706099712,94370803158936,94371179873921),(1706153984,94371224679898,94371601395194)]
theorem point_links_checked12986 : (cuts12986.take 3).map (fun c => (1706033153-1+2*2^9*c.k,94370287746667+c.lower,94370664461277+c.upper)) = pointBounds12986 := by
 decide +kernel
def cuts12987 : List PrefixCut := [⟨43,350072944,350073197⟩,
⟨96,773876733,773877293⟩,
⟨128,1024292357,1024293101⟩]
theorem checked12987 : checkPrefixCuts (2^48) 1706164225 9 Manual.Count131072.C012987.packed 128 cuts12987 = true := by
 decide +kernel
def pointBounds12987 : List (Nat × Nat × Nat) := [(1706208256,94371657900622,94372034616230),(1706262528,94372081704411,94372458420326)]
theorem point_links_checked12987 : (cuts12987.take 2).map (fun c => (1706164225-1+2*2^9*c.k,94371307827678+c.lower,94371684543033+c.upper)) = pointBounds12987 := by
 decide +kernel
def cuts12988 : List PrefixCut := [⟨21,165786368,165786487⟩,
⟨74,584779391,584779819⟩,
⟨127,1013986139,1013986875⟩,
⟨128,1022233637,1022234379⟩]
theorem checked12988 : checkPrefixCuts (2^48) 1706295297 9 Manual.Count131072.C012988.packed 128 cuts12988 = true := by
 decide +kernel
def pointBounds12988 : List (Nat × Nat × Nat) := [(1706316800,94372497906403,94372874622621),(1706371072,94372916899426,94373293615953),(1706425344,94373346106174,94373722823009)]
theorem point_links_checked12988 : (cuts12988.take 3).map (fun c => (1706295297-1+2*2^9*c.k,94372332120035+c.lower,94372708836134+c.upper)) = pointBounds12988 := by
 decide +kernel
def cuts12989 : List PrefixCut := [⟨52,409234354,409234656⟩,
⟨105,838413776,838414393⟩,
⟨128,1024464269,1024465024⟩]
theorem checked12989 : checkPrefixCuts (2^48) 1706426369 9 Manual.Count131072.C012989.packed 128 cuts12989 = true := by
 decide +kernel
def pointBounds12989 : List (Nat × Nat × Nat) := [(1706479616,94373763588026,94374140305169),(1706533888,94374192767448,94374569484906)]
theorem point_links_checked12989 : (cuts12989.take 2).map (fun c => (1706426369-1+2*2^9*c.k,94373354353672+c.lower,94373731070513+c.upper)) = pointBounds12989 := by
 decide +kernel
def cuts12990 : List PrefixCut := [⟨30,237342534,237342709⟩,
⟨83,662206474,662206953⟩,
⟨128,1014820013,1014820750⟩]
theorem checked12990 : checkPrefixCuts (2^48) 1706557441 9 Manual.Count131072.C012990.packed 128 cuts12990 = true := by
 decide +kernel
def pointBounds12990 : List (Nat × Nat × Nat) := [(1706588160,94374616160475,94374992878246),(1706642432,94375041024415,94375417742490)]
theorem point_links_checked12990 : (cuts12990.take 2).map (fun c => (1706557441-1+2*2^9*c.k,94374378817941+c.lower,94374755535537+c.upper)) = pointBounds12990 := by
 decide +kernel
def cuts12991 : List PrefixCut := [⟨8,65145053,65145100⟩,
⟨61,485199185,485199541⟩,
⟨114,910352335,910353004⟩,
⟨128,1019689402,1019690152⟩]
theorem checked12991 : checkPrefixCuts (2^48) 1706688513 9 Manual.Count131072.C012991.packed 128 cuts12991 = true := by
 decide +kernel
def pointBounds12991 : List (Nat × Nat × Nat) := [(1706696704,94375458783007,94375835501387),(1706750976,94375878837139,94376255555828),(1706805248,94376303990289,94376680709291)]
theorem point_links_checked12991 : (cuts12991.take 3).map (fun c => (1706688513-1+2*2^9*c.k,94375393637954+c.lower,94375770356287+c.upper)) = pointBounds12991 := by
 decide +kernel
def cuts12992 : List PrefixCut := [⟨39,307392189,307392416⟩,
⟨92,729385169,729385699⟩,
⟨128,1014828841,1014829577⟩]
theorem checked12992 : checkPrefixCuts (2^48) 1706819585 9 Manual.Count131072.C012992.packed 128 cuts12992 = true := by
 decide +kernel
def pointBounds12992 : List (Nat × Nat × Nat) := [(1706859520,94376720719545,94377097438855),(1706913792,94377142712525,94377519432138)]
theorem point_links_checked12992 : (cuts12992.take 2).map (fun c => (1706819585-1+2*2^9*c.k,94376413327356+c.lower,94376790046439+c.upper)) = pointBounds12992 := by
 decide +kernel
def cuts12993 : List PrefixCut := [⟨17,141153025,141153127⟩,
⟨70,555204181,555204584⟩,
⟨123,966439132,966439834⟩,
⟨128,1009144824,1009145555⟩]
theorem checked12993 : checkPrefixCuts (2^48) 1706950657 9 Manual.Count131072.C012993.packed 128 cuts12993 = true := by
 decide +kernel
def pointBounds12993 : List (Nat × Nat × Nat) := [(1706968064,94377569309222,94377946029143),(1707022336,94377983360378,94378360080600),(1707076608,94378394595329,94378771315850)]
theorem point_links_checked12993 : (cuts12993.take 3).map (fun c => (1706950657-1+2*2^9*c.k,94377428156197+c.lower,94377804876016+c.upper)) = pointBounds12993 := by
 decide +kernel
def cuts12994 : List PrefixCut := [⟨48,391435119,391435397⟩,
⟨101,815669383,815669967⟩,
⟨128,1024236574,1024237308⟩]
theorem checked12994 : checkPrefixCuts (2^48) 1707081729 9 Manual.Count131072.C012994.packed 128 cuts12994 = true := by
 decide +kernel
def pointBounds12994 : List (Nat × Nat × Nat) := [(1707130880,94378828736140,94379205456968),(1707185152,94379252970404,94379629691538)]
theorem point_links_checked12994 : (cuts12994.take 2).map (fun c => (1707081729-1+2*2^9*c.k,94378437301021+c.lower,94378814021571+c.upper)) = pointBounds12994 := by
 decide +kernel
def cuts12995 : List PrefixCut := [⟨26,203123109,203123257⟩,
⟨79,629638498,629638956⟩,
⟨128,1023168107,1023168845⟩]
theorem checked12995 : checkPrefixCuts (2^48) 1707212801 9 Manual.Count131072.C012995.packed 128 cuts12995 = true := by
 decide +kernel
def pointBounds12995 : List (Nat × Nat × Nat) := [(1707239424,94379664660704,94380041382136),(1707293696,94380091176093,94380467897835)]
theorem point_links_checked12995 : (cuts12995.take 2).map (fun c => (1707212801-1+2*2^9*c.k,94379461537595+c.lower,94379838258879+c.upper)) = pointBounds12995 := by
 decide +kernel
def cuts12996 : List PrefixCut := [⟨4,34950548,34950572⟩,
⟨57,450558200,450558526⟩,
⟨110,876373462,876374099⟩,
⟨128,1018803438,1018804181⟩]
theorem checked12996 : checkPrefixCuts (2^48) 1707343873 9 Manual.Count131072.C012996.packed 128 cuts12996 = true := by
 decide +kernel
def pointBounds12996 : List (Nat × Nat × Nat) := [(1707347968,94380519656250,94380896378296),(1707402240,94380935263902,94381311986250),(1707456512,94381361079164,94381737801823)]
theorem point_links_checked12996 : (cuts12996.take 3).map (fun c => (1707343873-1+2*2^9*c.k,94380484705702+c.lower,94380861427724+c.upper)) = pointBounds12996 := by
 decide +kernel
def cuts12997 : List PrefixCut := [⟨35,279745172,279745372⟩,
⟨88,695313108,695313611⟩,
⟨128,1007351311,1007352043⟩]
theorem checked12997 : checkPrefixCuts (2^48) 1707474945 9 Manual.Count131072.C012997.packed 128 cuts12997 = true := by
 decide +kernel
def pointBounds12997 : List (Nat × Nat × Nat) := [(1707510784,94381783254312,94382159977277),(1707565056,94382198822248,94382575545516)]
theorem point_links_checked12997 : (cuts12997.take 2).map (fun c => (1707474945-1+2*2^9*c.k,94381503509140+c.lower,94381880231905+c.upper)) = pointBounds12997 := by
 decide +kernel
def cuts12998 : List PrefixCut := [⟨13,101703395,101703470⟩,
⟨66,526310732,526311112⟩,
⟨119,943157676,943158359⟩,
⟨128,1018482129,1018482868⟩]
theorem checked12998 : checkPrefixCuts (2^48) 1707606017 9 Manual.Count131072.C012998.packed 128 cuts12998 = true := by
 decide +kernel
def pointBounds12998 : List (Nat × Nat × Nat) := [(1707619328,94382612563846,94382989287418),(1707673600,94383037171183,94383413895060),(1707727872,94383454018127,94383830742307)]
theorem point_links_checked12998 : (cuts12998.take 3).map (fun c => (1707606017-1+2*2^9*c.k,94382510860451+c.lower,94382887583948+c.upper)) = pointBounds12998 := by
 decide +kernel
def cuts12999 : List PrefixCut := [⟨44,355024681,355024933⟩,
⟨97,772834069,772834620⟩,
⟨128,1021535639,1021536368⟩]
theorem checked12999 : checkPrefixCuts (2^48) 1707737089 9 Manual.Count131072.C012999.packed 128 cuts12999 = true := by
 decide +kernel
def pointBounds12999 : List (Nat × Nat × Nat) := [(1707782144,94383884367261,94384261091749),(1707836416,94384302176649,94384678901436)]
theorem point_links_checked12999 : (cuts12999.take 2).map (fun c => (1707737089-1+2*2^9*c.k,94383529342580+c.lower,94383906066816+c.upper)) = pointBounds12999 := by
 decide +kernel
def cuts13000 : List PrefixCut := [⟨22,169259436,169259560⟩,
⟨75,591327177,591327604⟩,
⟨128,1013381624,1013382354⟩]
theorem checked13000 : checkPrefixCuts (2^48) 1707868161 9 Manual.Count131072.C013000.packed 128 cuts13000 = true := by
 decide +kernel
def pointBounds13000 : List (Nat × Nat × Nat) := [(1707890688,94384720137655,94385096862744),(1707944960,94385142205396,94385518930788),(1707999232,94385564259843,94385940985538)]
theorem point_links_checked13000 : (cuts13000.take 3).map (fun c => (1707868161-1+2*2^9*c.k,94384550878219+c.lower,94384927603184+c.upper)) = pointBounds13000 := by
 decide +kernel
def cuts13001 : List PrefixCut := [⟨53,421876178,421876486⟩,
⟨106,843903731,843904345⟩,
⟨128,1012974612,1012975351⟩]
theorem checked13001 : checkPrefixCuts (2^48) 1707999233 9 Manual.Count131072.C013001.packed 128 cuts13001 = true := by
 decide +kernel
def pointBounds13001 : List (Nat × Nat × Nat) := [(1708053504,94385986136021,94386362862024),(1708107776,94386408163574,94386784889883)]
theorem point_links_checked13001 : (cuts13001.take 2).map (fun c => (1707999233-1+2*2^9*c.k,94385564259843+c.lower,94385940985538+c.upper)) = pointBounds13001 := by
 decide +kernel
def cuts13002 : List PrefixCut := [⟨31,244703993,244704171⟩,
⟨84,662420513,662420999⟩,
⟨128,1013885421,1013886168⟩]
theorem checked13002 : checkPrefixCuts (2^48) 1708130305 9 Manual.Count131072.C013002.packed 128 cuts13002 = true := by
 decide +kernel
def pointBounds13002 : List (Nat × Nat × Nat) := [(1708162048,94386821938448,94387198665060),(1708216320,94387239654968,94387616381888)]
theorem point_links_checked13002 : (cuts13002.take 2).map (fun c => (1708130305-1+2*2^9*c.k,94386577234455+c.lower,94386953960889+c.upper)) = pointBounds13002 := by
 decide +kernel
def cuts13003 : List PrefixCut := [⟨9,66732769,66732817⟩,
⟨62,490189706,490190056⟩,
⟨115,911985484,911986138⟩,
⟨128,1012654285,1012655012⟩]
theorem checked13003 : checkPrefixCuts (2^48) 1708261377 9 Manual.Count131072.C013003.packed 128 cuts13003 = true := by
 decide +kernel
def pointBounds13003 : List (Nat × Nat × Nat) := [(1708270592,94387657852645,94388034579874),(1708324864,94388081309582,94388458037113),(1708379136,94388503105360,94388879833195)]
theorem point_links_checked13003 : (cuts13003.take 3).map (fun c => (1708261377-1+2*2^9*c.k,94387591119876+c.lower,94387967847057+c.upper)) = pointBounds13003 := by
 decide +kernel
def cuts13004 : List PrefixCut := [⟨40,314358509,314358736⟩,
⟨93,738598914,738599448⟩,
⟨128,1021143715,1021144455⟩]
theorem checked13004 : checkPrefixCuts (2^48) 1708392449 9 Manual.Count131072.C013004.packed 128 cuts13004 = true := by
 decide +kernel
def pointBounds13004 : List (Nat × Nat × Nat) := [(1708433408,94388918132670,94389294860805),(1708487680,94389342373075,94389719101517)]
theorem point_links_checked13004 : (cuts13004.take 2).map (fun c => (1708392449-1+2*2^9*c.k,94388603774161+c.lower,94388980502069+c.upper)) = pointBounds13004 := by
 decide +kernel
def cuts13005 : List PrefixCut := [⟨18,135915904,135916004⟩,
⟨71,552880503,552880906⟩,
⟨124,965383985,965384688⟩,
⟨128,997177843,997178569⟩]
theorem checked13005 : checkPrefixCuts (2^48) 1708523521 9 Manual.Count131072.C013005.packed 128 cuts13005 = true := by
 decide +kernel
def pointBounds13005 : List (Nat × Nat × Nat) := [(1708541952,94389760833780,94390137562528),(1708596224,94390177798379,94390554527430),(1708650496,94390590301861,94390967031212)]
theorem point_links_checked13005 : (cuts13005.take 3).map (fun c => (1708523521-1+2*2^9*c.k,94389624917876+c.lower,94390001646524+c.upper)) = pointBounds13005 := by
 decide +kernel
def cuts13006 : List PrefixCut := [⟨49,384650079,384650363⟩,
⟨102,798939353,798939940⟩,
⟨128,1013738706,1013739450⟩]
theorem checked13006 : checkPrefixCuts (2^48) 1708654593 9 Manual.Count131072.C013006.packed 128 cuts13006 = true := by
 decide +kernel
def pointBounds13006 : List (Nat × Nat × Nat) := [(1708704768,94391006745798,94391383475456),(1708759040,94391421035072,94391797765033)]
theorem point_links_checked13006 : (cuts13006.take 2).map (fun c => (1708654593-1+2*2^9*c.k,94390622095719+c.lower,94390998825093+c.upper)) = pointBounds13006 := by
 decide +kernel
def cuts13007 : List PrefixCut := [⟨27,209689633,209689784⟩,
⟨80,621481863,621482317⟩,
⟨128,1007401897,1007402621⟩]
theorem checked13007 : checkPrefixCuts (2^48) 1708785665 9 Manual.Count131072.C013007.packed 128 cuts13007 = true := by
 decide +kernel
def pointBounds13007 : List (Nat × Nat × Nat) := [(1708813312,94391845524058,94392222254327),(1708867584,94392257316288,94392634046860)]
theorem point_links_checked13007 : (cuts13007.take 2).map (fun c => (1708785665-1+2*2^9*c.k,94391635834425+c.lower,94392012564543+c.upper)) = pointBounds13007 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000093
