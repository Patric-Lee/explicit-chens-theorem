import PlattAssemblyKernel
import PlattCertificates.Count131072.C021024
import PlattCertificates.Count131072.C021025
import PlattCertificates.Count131072.C021026
import PlattCertificates.Count131072.C021027
import PlattCertificates.Count131072.C021028
import PlattCertificates.Count131072.C021029
import PlattCertificates.Count131072.C021030
import PlattCertificates.Count131072.C021031
import PlattCertificates.Count131072.C021032
import PlattCertificates.Count131072.C021033
import PlattCertificates.Count131072.C021034
import PlattCertificates.Count131072.C021035
import PlattCertificates.Count131072.C021036
import PlattCertificates.Count131072.C021037
import PlattCertificates.Count131072.C021038
import PlattCertificates.Count131072.C021039
import PlattCertificates.Count131072.C021040
import PlattCertificates.Count131072.C021041
import PlattCertificates.Count131072.C021042
import PlattCertificates.Count131072.C021043
import PlattCertificates.Count131072.C021044
import PlattCertificates.Count131072.C021045
import PlattCertificates.Count131072.C021046
import PlattCertificates.Count131072.C021047
import PlattCertificates.Count131072.C021048
import PlattCertificates.Count131072.C021049
import PlattCertificates.Count131072.C021050
import PlattCertificates.Count131072.C021051
import PlattCertificates.Count131072.C021052
import PlattCertificates.Count131072.C021053
import PlattCertificates.Count131072.C021054
import PlattCertificates.Count131072.C021055
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000032
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts21024 : List PrefixCut := [⟨34,158403161,158403256⟩,
⟨119,566284841,566285174⟩,
⟨128,608408419,608408777⟩]
theorem checked21024 : checkPrefixCuts (2^48) 2759589889 9 Manual.Count131072.C021024.packed 128 cuts21024 = true := by
 decide +kernel
def pointBounds21024 : List (Nat × Nat × Nat) := [(2759624704,100667241900427,100667622647218),(2759711744,100667649782107,100668030529136)]
theorem point_links_checked21024 : (cuts21024.take 2).map (fun c => (2759589889-1+2*2^9*c.k,100667083497266+c.lower,100667464243962+c.upper)) = pointBounds21024 := by
 decide +kernel
def cuts21025 : List PrefixCut := [⟨76,369518874,369519087⟩,
⟨128,617048837,617049195⟩]
theorem checked21025 : checkPrefixCuts (2^48) 2759720961 9 Manual.Count131072.C021025.packed 128 cuts21025 = true := by
 decide +kernel
def pointBounds21025 : List (Nat × Nat × Nat) := [(2759798784,100668061424559,100668442171826)]
theorem point_links_checked21025 : (cuts21025.take 1).map (fun c => (2759720961-1+2*2^9*c.k,100667691905685+c.lower,100668072652739+c.upper)) = pointBounds21025 := by
 decide +kernel
def cuts21026 : List PrefixCut := [⟨33,155532455,155532542⟩,
⟨118,560621906,560622229⟩,
⟨128,610288344,610288696⟩]
theorem checked21026 : checkPrefixCuts (2^48) 2759852033 9 Manual.Count131072.C021026.packed 128 cuts21026 = true := by
 decide +kernel
def pointBounds21026 : List (Nat × Nat × Nat) := [(2759885824,100668464486977,100668845234476),(2759972864,100668869576428,100669250324163)]
theorem point_links_checked21026 : (cuts21026.take 2).map (fun c => (2759852033-1+2*2^9*c.k,100668308954522+c.lower,100668689701934+c.upper)) = pointBounds21026 := by
 decide +kernel
def cuts21027 : List PrefixCut := [⟨75,364180764,364180979⟩,
⟨128,618214025,618214392⟩]
theorem checked21027 : checkPrefixCuts (2^48) 2759983105 9 Manual.Count131072.C021027.packed 128 cuts21027 = true := by
 decide +kernel
def pointBounds21027 : List (Nat × Nat × Nat) := [(2760059904,100669283423630,100669664171609)]
theorem point_links_checked21027 : (cuts21027.take 1).map (fun c => (2759983105-1+2*2^9*c.k,100668919242866+c.lower,100669299990630+c.upper)) = pointBounds21027 := by
 decide +kernel
def cuts21028 : List PrefixCut := [⟨32,150010873,150010961⟩,
⟨117,560160807,560161139⟩,
⟨128,613391657,613392019⟩]
theorem checked21028 : checkPrefixCuts (2^48) 2760114177 9 Manual.Count131072.C021028.packed 128 cuts21028 = true := by
 decide +kernel
def pointBounds21028 : List (Nat × Nat × Nat) := [(2760146944,100669687467764,100670068215983),(2760233984,100670097617698,100670478366161)]
theorem point_links_checked21028 : (cuts21028.take 2).map (fun c => (2760114177-1+2*2^9*c.k,100669537456891+c.lower,100669918205022+c.upper)) = pointBounds21028 := by
 decide +kernel
def cuts21029 : List PrefixCut := [⟨74,350073965,350074169⟩,
⟨128,604898961,604899317⟩]
theorem checked21029 : checkPrefixCuts (2^48) 2760245249 9 Manual.Count131072.C021029.packed 128 cuts21029 = true := by
 decide +kernel
def pointBounds21029 : List (Nat × Nat × Nat) := [(2760321024,100670500922513,100670881671210)]
theorem point_links_checked21029 : (cuts21029.take 1).map (fun c => (2760245249-1+2*2^9*c.k,100670150848548+c.lower,100670531597041+c.upper)) = pointBounds21029 := by
 decide +kernel
def cuts21030 : List PrefixCut := [⟨31,149792723,149792811⟩,
⟨116,555519302,555519623⟩,
⟨128,612313887,612314239⟩]
theorem checked21030 : checkPrefixCuts (2^48) 2760376321 9 Manual.Count131072.C021030.packed 128 cuts21030 = true := by
 decide +kernel
def pointBounds21030 : List (Nat × Nat × Nat) := [(2760408064,100670905540232,100671286289169),(2760495104,100671311266811,100671692015981)]
theorem point_links_checked21030 : (cuts21030.take 2).map (fun c => (2760376321-1+2*2^9*c.k,100670755747509+c.lower,100671136496358+c.upper)) = pointBounds21030 := by
 decide +kernel
def cuts21031 : List PrefixCut := [⟨73,347695627,347695830⟩,
⟨128,615139645,615140002⟩]
theorem checked21031 : checkPrefixCuts (2^48) 2760507393 9 Manual.Count131072.C021031.packed 128 cuts21031 = true := by
 decide +kernel
def pointBounds21031 : List (Nat × Nat × Nat) := [(2760582144,100671715757023,100672096506427)]
theorem point_links_checked21031 : (cuts21031.take 1).map (fun c => (2760507393-1+2*2^9*c.k,100671368061396+c.lower,100671748810597+c.upper)) = pointBounds21031 := by
 decide +kernel
def cuts21032 : List PrefixCut := [⟨30,144476605,144476689⟩,
⟨115,555772455,555772779⟩,
⟨128,617761385,617761746⟩]
theorem checked21032 : checkPrefixCuts (2^48) 2760638465 9 Manual.Count131072.C021032.packed 128 cuts21032 = true := by
 decide +kernel
def pointBounds21032 : List (Nat × Nat × Nat) := [(2760669184,100672127677646,100672508427288),(2760756224,100672538973496,100672919723378)]
theorem point_links_checked21032 : (cuts21032.take 2).map (fun c => (2760638465-1+2*2^9*c.k,100671983201041+c.lower,100672363950599+c.upper)) = pointBounds21032 := by
 decide +kernel
def cuts21033 : List PrefixCut := [⟨72,346541211,346541411⟩,
⟨128,617630084,617630439⟩]
theorem checked21033 : checkPrefixCuts (2^48) 2760769537 9 Manual.Count131072.C021033.packed 128 cuts21033 = true := by
 decide +kernel
def pointBounds21033 : List (Nat × Nat × Nat) := [(2760843264,100672947503637,100673328253756)]
theorem point_links_checked21033 : (cuts21033.take 1).map (fun c => (2760769537-1+2*2^9*c.k,100672600962426+c.lower,100672981712345+c.upper)) = pointBounds21033 := by
 decide +kernel
def cuts21034 : List PrefixCut := [⟨29,141098577,141098659⟩,
⟨114,550010727,550011047⟩,
⟨128,620965013,620965376⟩]
theorem checked21034 : checkPrefixCuts (2^48) 2760900609 9 Manual.Count131072.C021034.packed 128 cuts21034 = true := by
 decide +kernel
def pointBounds21034 : List (Nat × Nat × Nat) := [(2760930304,100673359691087,100673740441443),(2761017344,100673768603237,100674149353831)]
theorem point_links_checked21034 : (cuts21034.take 2).map (fun c => (2760900609-1+2*2^9*c.k,100673218592510+c.lower,100673599342784+c.upper)) = pointBounds21034 := by
 decide +kernel
def cuts21035 : List PrefixCut := [⟨71,336517855,336518053⟩,
⟨128,604013080,604013438⟩]
theorem checked21035 : checkPrefixCuts (2^48) 2761031681 9 Manual.Count131072.C021035.packed 128 cuts21035 = true := by
 decide +kernel
def pointBounds21035 : List (Nat × Nat × Nat) := [(2761104384,100674176075378,100674556826213)]
theorem point_links_checked21035 : (cuts21035.take 1).map (fun c => (2761031681-1+2*2^9*c.k,100673839557523+c.lower,100674220308160+c.upper)) = pointBounds21035 := by
 decide +kernel
def cuts21036 : List PrefixCut := [⟨28,133439698,133439776⟩,
⟨113,530488419,530488731⟩,
⟨128,605309557,605309910⟩]
theorem checked21036 : checkPrefixCuts (2^48) 2761162753 9 Manual.Count131072.C021036.packed 128 cuts21036 = true := by
 decide +kernel
def pointBounds21036 : List (Nat × Nat × Nat) := [(2761191424,100674577010301,100674957761374),(2761278464,100674974059022,100675354810329)]
theorem point_links_checked21036 : (cuts21036.take 2).map (fun c => (2761162753-1+2*2^9*c.k,100674443570603+c.lower,100674824321598+c.upper)) = pointBounds21036 := by
 decide +kernel
def cuts21037 : List PrefixCut := [⟨70,335364644,335364835⟩,
⟨128,618124339,618124691⟩]
theorem checked21037 : checkPrefixCuts (2^48) 2761293825 9 Manual.Count131072.C021037.packed 128 cuts21037 = true := by
 decide +kernel
def pointBounds21037 : List (Nat × Nat × Nat) := [(2761365504,100675384244804,100675764996343)]
theorem point_links_checked21037 : (cuts21037.take 1).map (fun c => (2761293825-1+2*2^9*c.k,100675048880160+c.lower,100675429631508+c.upper)) = pointBounds21037 := by
 decide +kernel
def cuts21038 : List PrefixCut := [⟨27,132611616,132611689⟩,
⟨112,536350064,536350365⟩,
⟨128,615445018,615445367⟩]
theorem checked21038 : checkPrefixCuts (2^48) 2761424897 9 Manual.Count131072.C021038.packed 128 cuts21038 = true := by
 decide +kernel
def pointBounds21038 : List (Nat × Nat × Nat) := [(2761452544,100675799616115,100676180367888),(2761539584,100676203354563,100676584106564)]
theorem point_links_checked21038 : (cuts21038.take 2).map (fun c => (2761424897-1+2*2^9*c.k,100675667004499+c.lower,100676047756199+c.upper)) = pointBounds21038 := by
 decide +kernel
def cuts21039 : List PrefixCut := [⟨69,335332890,335333081⟩,
⟨128,617454350,617454710⟩]
theorem checked21039 : checkPrefixCuts (2^48) 2761555969 9 Manual.Count131072.C021039.packed 128 cuts21039 = true := by
 decide +kernel
def pointBounds21039 : List (Nat × Nat × Nat) := [(2761626624,100676617782407,100676998534647)]
theorem point_links_checked21039 : (cuts21039.take 1).map (fun c => (2761555969-1+2*2^9*c.k,100676282449517+c.lower,100676663201566+c.upper)) = pointBounds21039 := by
 decide +kernel
def cuts21040 : List PrefixCut := [⟨26,128624149,128624222⟩,
⟨111,535381933,535382245⟩,
⟨128,618851823,618852184⟩]
theorem checked21040 : checkPrefixCuts (2^48) 2761687041 9 Manual.Count131072.C021040.packed 128 cuts21040 = true := by
 decide +kernel
def pointBounds21040 : List (Nat × Nat × Nat) := [(2761713664,100677028528016,100677409280498),(2761800704,100677435285800,100677816038521)]
theorem point_links_checked21040 : (cuts21040.take 2).map (fun c => (2761687041-1+2*2^9*c.k,100676899903867+c.lower,100677280656276+c.upper)) = pointBounds21040 := by
 decide +kernel
def cuts21041 : List PrefixCut := [⟨68,323580931,323581121⟩,
⟨128,608936813,608937170⟩]
theorem checked21041 : checkPrefixCuts (2^48) 2761818113 9 Manual.Count131072.C021041.packed 128 cuts21041 = true := by
 decide +kernel
def pointBounds21041 : List (Nat × Nat × Nat) := [(2761887744,100677842336621,100678223089581)]
theorem point_links_checked21041 : (cuts21041.take 1).map (fun c => (2761818113-1+2*2^9*c.k,100677518755690+c.lower,100677899508460+c.upper)) = pointBounds21041 := by
 decide +kernel
def cuts21042 : List PrefixCut := [⟨25,120357138,120357208⟩,
⟨110,535840655,535840960⟩,
⟨128,621748410,621748767⟩]
theorem checked21042 : checkPrefixCuts (2^48) 2761949185 9 Manual.Count131072.C021042.packed 128 cuts21042 = true := by
 decide +kernel
def pointBounds21042 : List (Nat × Nat × Nat) := [(2761974784,100678248049641,100678628802838),(2762061824,100678663533158,100679044286590)]
theorem point_links_checked21042 : (cuts21042.take 2).map (fun c => (2761949185-1+2*2^9*c.k,100678127692503+c.lower,100678508445630+c.upper)) = pointBounds21042 := by
 decide +kernel
def cuts21043 : List PrefixCut := [⟨67,324773081,324773267⟩,
⟨128,618763709,618764066⟩]
theorem checked21043 : checkPrefixCuts (2^48) 2762080257 9 Manual.Count131072.C021043.packed 128 cuts21043 = true := by
 decide +kernel
def pointBounds21043 : List (Nat × Nat × Nat) := [(2762148864,100679074213994,100679454967664)]
theorem point_links_checked21043 : (cuts21043.take 1).map (fun c => (2762080257-1+2*2^9*c.k,100678749440913+c.lower,100679130194397+c.upper)) = pointBounds21043 := by
 decide +kernel
def cuts21044 : List PrefixCut := [⟨24,117492506,117492574⟩,
⟨109,522135388,522135692⟩,
⟨128,612518504,612518860⟩]
theorem checked21044 : checkPrefixCuts (2^48) 2762211329 9 Manual.Count131072.C021044.packed 128 cuts21044 = true := by
 decide +kernel
def pointBounds21044 : List (Nat × Nat × Nat) := [(2762235904,100679485697128,100679866451037),(2762322944,100679890340010,100680271094155)]
theorem point_links_checked21044 : (cuts21044.take 2).map (fun c => (2762211329-1+2*2^9*c.k,100679368204622+c.lower,100679748958463+c.upper)) = pointBounds21044 := by
 decide +kernel
def cuts21045 : List PrefixCut := [⟨66,315367932,315368114⟩,
⟨128,607190945,607191301⟩]
theorem checked21045 : checkPrefixCuts (2^48) 2762342401 9 Manual.Count131072.C021045.packed 128 cuts21045 = true := by
 decide +kernel
def pointBounds21045 : List (Nat × Nat × Nat) := [(2762409984,100680296091058,100680676845437)]
theorem point_links_checked21045 : (cuts21045.take 1).map (fun c => (2762342401-1+2*2^9*c.k,100679980723126+c.lower,100680361477323+c.upper)) = pointBounds21045 := by
 decide +kernel
def cuts21046 : List PrefixCut := [⟨23,109126230,109126292⟩,
⟨108,516176275,516176573⟩,
⟨128,613071653,613072006⟩]
theorem checked21046 : checkPrefixCuts (2^48) 2762473473 9 Manual.Count131072.C021046.packed 128 cuts21046 = true := by
 decide +kernel
def pointBounds21046 : List (Nat × Nat × Nat) := [(2762497024,100680697040301,100681077794916),(2762584064,100681104090346,100681484845197)]
theorem point_links_checked21046 : (cuts21046.take 2).map (fun c => (2762473473-1+2*2^9*c.k,100680587914071+c.lower,100680968668624+c.upper)) = pointBounds21046 := by
 decide +kernel
def cuts21047 : List PrefixCut := [⟨65,309938106,309938290⟩,
⟨128,621091438,621091803⟩]
theorem checked21047 : checkPrefixCuts (2^48) 2762604545 9 Manual.Count131072.C021047.packed 128 cuts21047 = true := by
 decide +kernel
def pointBounds21047 : List (Nat × Nat × Nat) := [(2762671104,100681510923830,100681891678920)]
theorem point_links_checked21047 : (cuts21047.take 1).map (fun c => (2762604545-1+2*2^9*c.k,100681200985724+c.lower,100681581740630+c.upper)) = pointBounds21047 := by
 decide +kernel
def cuts21048 : List PrefixCut := [⟨22,104633074,104633134⟩,
⟨107,508384431,508384730⟩,
⟨128,609447639,609447998⟩]
theorem checked21048 : checkPrefixCuts (2^48) 2762735617 9 Manual.Count131072.C021048.packed 128 cuts21048 = true := by
 decide +kernel
def pointBounds21048 : List (Nat × Nat × Nat) := [(2762758144,100681926710236,100682307465567),(2762845184,100682330461593,100682711217163)]
theorem point_links_checked21048 : (cuts21048.take 2).map (fun c => (2762735617-1+2*2^9*c.k,100681822077162+c.lower,100682202832433+c.upper)) = pointBounds21048 := by
 decide +kernel
def cuts21049 : List PrefixCut := [⟨64,312353770,312353950⟩,
⟨128,618078297,618078653⟩]
theorem checked21049 : checkPrefixCuts (2^48) 2762866689 9 Manual.Count131072.C021049.packed 128 cuts21049 = true := by
 decide +kernel
def pointBounds21049 : List (Nat × Nat × Nat) := [(2762932224,100682743878571,100683124634381)]
theorem point_links_checked21049 : (cuts21049.take 1).map (fun c => (2762866689-1+2*2^9*c.k,100682431524801+c.lower,100682812280431+c.upper)) = pointBounds21049 := by
 decide +kernel
def cuts21050 : List PrefixCut := [⟨21,104928799,104928857⟩,
⟨106,511392544,511392833⟩,
⟨128,618150833,618151184⟩]
theorem checked21050 : checkPrefixCuts (2^48) 2762997761 9 Manual.Count131072.C021050.packed 128 cuts21050 = true := by
 decide +kernel
def pointBounds21050 : List (Nat × Nat × Nat) := [(2763019264,100683154531897,100683535287941),(2763106304,100683560995642,100683941751917)]
theorem point_links_checked21050 : (cuts21050.take 2).map (fun c => (2762997761-1+2*2^9*c.k,100683049603098+c.lower,100683430359084+c.upper)) = pointBounds21050 := by
 decide +kernel
def cuts21051 : List PrefixCut := [⟨63,307434591,307434766⟩,
⟨128,619751360,619751719⟩]
theorem checked21051 : checkPrefixCuts (2^48) 2763128833 9 Manual.Count131072.C021051.packed 128 cuts21051 = true := by
 decide +kernel
def pointBounds21051 : List (Nat × Nat × Nat) := [(2763193344,100683975188522,100684355945034)]
theorem point_links_checked21051 : (cuts21051.take 1).map (fun c => (2763128833-1+2*2^9*c.k,100683667753931+c.lower,100684048510268+c.upper)) = pointBounds21051 := by
 decide +kernel
def cuts21052 : List PrefixCut := [⟨20,97380995,97381051⟩,
⟨105,507575155,507575442⟩,
⟨128,617990256,617990609⟩]
theorem checked21052 : checkPrefixCuts (2^48) 2763259905 9 Manual.Count131072.C021052.packed 128 cuts21052 = true := by
 decide +kernel
def pointBounds21052 : List (Nat × Nat × Nat) := [(2763280384,100684384886286,100684765643038),(2763367424,100684795080446,100685175837429)]
theorem point_links_checked21052 : (cuts21052.take 2).map (fun c => (2763259905-1+2*2^9*c.k,100684287505291+c.lower,100684668261987+c.upper)) = pointBounds21052 := by
 decide +kernel
def cuts21053 : List PrefixCut := [⟨62,301192143,301192311⟩,
⟨128,613377458,613377805⟩]
theorem checked21053 : checkPrefixCuts (2^48) 2763390977 9 Manual.Count131072.C021053.packed 128 cuts21053 = true := by
 decide +kernel
def pointBounds21053 : List (Nat × Nat × Nat) := [(2763454464,100685206687690,100685587444907)]
theorem point_links_checked21053 : (cuts21053.take 1).map (fun c => (2763390977-1+2*2^9*c.k,100684905495547+c.lower,100685286252596+c.upper)) = pointBounds21053 := by
 decide +kernel
def cuts21054 : List PrefixCut := [⟨19,91667989,91668042⟩,
⟨104,498971547,498971834⟩,
⟨128,610903923,610904277⟩]
theorem checked21054 : checkPrefixCuts (2^48) 2763522049 9 Manual.Count131072.C021054.packed 128 cuts21054 = true := by
 decide +kernel
def pointBounds21054 : List (Nat × Nat × Nat) := [(2763541504,100685610540994,100685991298443),(2763628544,100686017844552,100686398602235)]
theorem point_links_checked21054 : (cuts21054.take 2).map (fun c => (2763522049-1+2*2^9*c.k,100685518873005+c.lower,100685899630401+c.upper)) = pointBounds21054 := by
 decide +kernel
def cuts21055 : List PrefixCut := [⟨61,288330845,288331012⟩,
⟨128,607615833,607616187⟩]
theorem checked21055 : checkPrefixCuts (2^48) 2763653121 9 Manual.Count131072.C021055.packed 128 cuts21055 = true := by
 decide +kernel
def pointBounds21055 : List (Nat × Nat × Nat) := [(2763715584,100686418107773,100686798865690)]
theorem point_links_checked21055 : (cuts21055.take 1).map (fun c => (2763653121-1+2*2^9*c.k,100686129776928+c.lower,100686510534678+c.upper)) = pointBounds21055 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000032
