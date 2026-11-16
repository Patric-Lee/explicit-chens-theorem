import PlattAssemblyKernel
import PlattCertificates.Count131072.C045984
import PlattCertificates.Count131072.C045985
import PlattCertificates.Count131072.C045986
import PlattCertificates.Count131072.C045987
import PlattCertificates.Count131072.C045988
import PlattCertificates.Count131072.C045989
import PlattCertificates.Count131072.C045990
import PlattCertificates.Count131072.C045991
import PlattCertificates.Count131072.C045992
import PlattCertificates.Count131072.C045993
import PlattCertificates.Count131072.C045994
import PlattCertificates.Count131072.C045995
import PlattCertificates.Count131072.C045996
import PlattCertificates.Count131072.C045997
import PlattCertificates.Count131072.C045998
import PlattCertificates.Count131072.C045999
import PlattCertificates.Count131072.C046000
import PlattCertificates.Count131072.C046001
import PlattCertificates.Count131072.C046002
import PlattCertificates.Count131072.C046003
import PlattCertificates.Count131072.C046004
import PlattCertificates.Count131072.C046005
import PlattCertificates.Count131072.C046006
import PlattCertificates.Count131072.C046007
import PlattCertificates.Count131072.C046008
import PlattCertificates.Count131072.C046009
import PlattCertificates.Count131072.C046010
import PlattCertificates.Count131072.C046011
import PlattCertificates.Count131072.C046012
import PlattCertificates.Count131072.C046013
import PlattCertificates.Count131072.C046014
import PlattCertificates.Count131072.C046015
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000187
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts45984 : List PrefixCut := [⟨64,272737730,272737888⟩]
theorem checked45984 : checkPrefixCuts (2^48) 6031147009 10 Manual.Count131072.C045984.packed 64 cuts45984 = true := by
 decide +kernel
def cuts45985 : List PrefixCut := [⟨20,87691119,87691171⟩,
⟨64,273851866,273852024⟩]
theorem checked45985 : checkPrefixCuts (2^48) 6031278081 10 Manual.Count131072.C045985.packed 64 cuts45985 = true := by
 decide +kernel
def pointBounds45985 : List (Nat × Nat × Nat) := [(6031319040,110613285579915,110613672105101)]
theorem point_links_checked45985 : (cuts45985.take 1).map (fun c => (6031278081-1+2*2^10*c.k,110613197888796+c.lower,110613584413930+c.upper)) = pointBounds45985 := by
 decide +kernel
def cuts45986 : List PrefixCut := [⟨49,209538390,209538513⟩,
⟨64,273565906,273566062⟩]
theorem checked45986 : checkPrefixCuts (2^48) 6031409153 10 Manual.Count131072.C045986.packed 64 cuts45986 = true := by
 decide +kernel
def pointBounds45986 : List (Nat × Nat × Nat) := [(6031509504,110613681279052,110614067804467)]
theorem point_links_checked45986 : (cuts45986.take 1).map (fun c => (6031409153-1+2*2^10*c.k,110613471740662+c.lower,110613858265954+c.upper)) = pointBounds45986 := by
 decide +kernel
def cuts45987 : List PrefixCut := [⟨64,270479991,270480144⟩]
theorem checked45987 : checkPrefixCuts (2^48) 6031540225 10 Manual.Count131072.C045987.packed 64 cuts45987 = true := by
 decide +kernel
def cuts45988 : List PrefixCut := [⟨14,61459179,61459213⟩,
⟨64,271780746,271780895⟩]
theorem checked45988 : checkPrefixCuts (2^48) 6031671297 10 Manual.Count131072.C045988.packed 64 cuts45988 = true := by
 decide +kernel
def pointBounds45988 : List (Nat × Nat × Nat) := [(6031699968,110614077245738,110614463771373)]
theorem point_links_checked45988 : (cuts45988.take 1).map (fun c => (6031671297-1+2*2^10*c.k,110614015786559+c.lower,110614402312160+c.upper)) = pointBounds45988 := by
 decide +kernel
def cuts45989 : List PrefixCut := [⟨43,182086045,182086147⟩,
⟨64,274901319,274901473⟩]
theorem checked45989 : checkPrefixCuts (2^48) 6031802369 10 Manual.Count131072.C045989.packed 64 cuts45989 = true := by
 decide +kernel
def pointBounds45989 : List (Nat × Nat × Nat) := [(6031890432,110614469653350,110614856179202)]
theorem point_links_checked45989 : (cuts45989.take 1).map (fun c => (6031802369-1+2*2^10*c.k,110614287567305+c.lower,110614674093055+c.upper)) = pointBounds45989 := by
 decide +kernel
def cuts45990 : List PrefixCut := [⟨64,274008760,274008919⟩]
theorem checked45990 : checkPrefixCuts (2^48) 6031933441 10 Manual.Count131072.C045990.packed 64 cuts45990 = true := by
 decide +kernel
def cuts45991 : List PrefixCut := [⟨8,34017360,34017381⟩,
⟨64,268916618,268916771⟩]
theorem checked45991 : checkPrefixCuts (2^48) 6032064513 10 Manual.Count131072.C045991.packed 64 cuts45991 = true := by
 decide +kernel
def pointBounds45991 : List (Nat × Nat × Nat) := [(6032080896,110614870494744,110615257020828)]
theorem point_links_checked45991 : (cuts45991.take 1).map (fun c => (6032064513-1+2*2^10*c.k,110614836477384+c.lower,110615223003447+c.upper)) = pointBounds45991 := by
 decide +kernel
def cuts45992 : List PrefixCut := [⟨37,155523802,155523892⟩,
⟨64,268350808,268350966⟩]
theorem checked45992 : checkPrefixCuts (2^48) 6032195585 10 Manual.Count131072.C045992.packed 64 cuts45992 = true := by
 decide +kernel
def pointBounds45992 : List (Nat × Nat × Nat) := [(6032271360,110615260917804,110615647444110)]
theorem point_links_checked45992 : (cuts45992.take 1).map (fun c => (6032195585-1+2*2^10*c.k,110615105394002+c.lower,110615491920218+c.upper)) = pointBounds45992 := by
 decide +kernel
def cuts45993 : List PrefixCut := [⟨64,271564572,271564724⟩]
theorem checked45993 : checkPrefixCuts (2^48) 6032326657 10 Manual.Count131072.C045993.packed 64 cuts45993 = true := by
 decide +kernel
def cuts45994 : List PrefixCut := [⟨2,8305489,8305494⟩,
⟨64,270158837,270159001⟩]
theorem checked45994 : checkPrefixCuts (2^48) 6032457729 10 Manual.Count131072.C045994.packed 64 cuts45994 = true := by
 decide +kernel
def pointBounds45994 : List (Nat × Nat × Nat) := [(6032461824,110615653614871,110616040141402)]
theorem point_links_checked45994 : (cuts45994.take 1).map (fun c => (6032457729-1+2*2^10*c.k,110615645309382+c.lower,110616031835908+c.upper)) = pointBounds45994 := by
 decide +kernel
def cuts45995 : List PrefixCut := [⟨31,129618171,129618247⟩,
⟨64,269826370,269826535⟩]
theorem checked45995 : checkPrefixCuts (2^48) 6032588801 10 Manual.Count131072.C045995.packed 64 cuts45995 = true := by
 decide +kernel
def pointBounds45995 : List (Nat × Nat × Nat) := [(6032652288,110616045086390,110616431613156)]
theorem point_links_checked45995 : (cuts45995.take 1).map (fun c => (6032588801-1+2*2^10*c.k,110615915468219+c.lower,110616301994909+c.upper)) = pointBounds45995 := by
 decide +kernel
def cuts45996 : List PrefixCut := [⟨60,255776764,255776910⟩,
⟨64,272340019,272340177⟩]
theorem checked45996 : checkPrefixCuts (2^48) 6032719873 10 Manual.Count131072.C045996.packed 64 cuts45996 = true := by
 decide +kernel
def pointBounds45996 : List (Nat × Nat × Nat) := [(6032842752,110616441071353,110616827598354)]
theorem point_links_checked45996 : (cuts45996.take 1).map (fun c => (6032719873-1+2*2^10*c.k,110616185294589+c.lower,110616571821444+c.upper)) = pointBounds45996 := by
 decide +kernel
def cuts45997 : List PrefixCut := [⟨64,272007532,272007692⟩]
theorem checked45997 : checkPrefixCuts (2^48) 6032850945 10 Manual.Count131072.C045997.packed 64 cuts45997 = true := by
 decide +kernel
def cuts45998 : List PrefixCut := [⟨25,102269552,102269611⟩,
⟨64,267475998,267476152⟩]
theorem checked45998 : checkPrefixCuts (2^48) 6032982017 10 Manual.Count131072.C045998.packed 64 cuts45998 = true := by
 decide +kernel
def pointBounds45998 : List (Nat × Nat × Nat) := [(6033033216,110616831911692,110617218438924)]
theorem point_links_checked45998 : (cuts45998.take 1).map (fun c => (6032982017-1+2*2^10*c.k,110616729642140+c.lower,110617116169313+c.upper)) = pointBounds45998 := by
 decide +kernel
def cuts45999 : List PrefixCut := [⟨54,229120612,229120738⟩,
⟨64,272228970,272229120⟩]
theorem checked45999 : checkPrefixCuts (2^48) 6033113089 10 Manual.Count131072.C045999.packed 64 cuts45999 = true := by
 decide +kernel
def pointBounds45999 : List (Nat × Nat × Nat) := [(6033223680,110617226238750,110617612766203)]
theorem point_links_checked45999 : (cuts45999.take 1).map (fun c => (6033113089-1+2*2^10*c.k,110616997118138+c.lower,110617383645465+c.upper)) = pointBounds45999 := by
 decide +kernel
def cuts46000 : List PrefixCut := [⟨64,273062820,273062976⟩]
theorem checked46000 : checkPrefixCuts (2^48) 6033244161 10 Manual.Count131072.C046000.packed 64 cuts46000 = true := by
 decide +kernel
def cuts46001 : List PrefixCut := [⟨19,82528848,82528895⟩,
⟨64,275482828,275482981⟩]
theorem checked46001 : checkPrefixCuts (2^48) 6033375233 10 Manual.Count131072.C046001.packed 64 cuts46001 = true := by
 decide +kernel
def pointBounds46001 : List (Nat × Nat × Nat) := [(6033414144,110617624938776,110618011466456)]
theorem point_links_checked46001 : (cuts46001.take 1).map (fun c => (6033375233-1+2*2^10*c.k,110617542409928+c.lower,110617928937561+c.upper)) = pointBounds46001 := by
 decide +kernel
def cuts46002 : List PrefixCut := [⟨48,201861404,201861522⟩,
⟨64,268525790,268525948⟩]
theorem checked46002 : checkPrefixCuts (2^48) 6033506305 10 Manual.Count131072.C046002.packed 64 cuts46002 = true := by
 decide +kernel
def pointBounds46002 : List (Nat × Nat × Nat) := [(6033604608,110618019754160,110618406282064)]
theorem point_links_checked46002 : (cuts46002.take 1).map (fun c => (6033506305-1+2*2^10*c.k,110617817892756+c.lower,110618204420542+c.upper)) = pointBounds46002 := by
 decide +kernel
def cuts46003 : List PrefixCut := [⟨64,271692154,271692308⟩]
theorem checked46003 : checkPrefixCuts (2^48) 6033637377 10 Manual.Count131072.C046003.packed 64 cuts46003 = true := by
 decide +kernel
def cuts46004 : List PrefixCut := [⟨13,57006091,57006124⟩,
⟨64,272572598,272572758⟩]
theorem checked46004 : checkPrefixCuts (2^48) 6033768449 10 Manual.Count131072.C046004.packed 64 cuts46004 = true := by
 decide +kernel
def pointBounds46004 : List (Nat × Nat × Nat) := [(6033795072,110618415116791,110618801644922)]
theorem point_links_checked46004 : (cuts46004.take 1).map (fun c => (6033768449-1+2*2^10*c.k,110618358110700+c.lower,110618744638798+c.upper)) = pointBounds46004 := by
 decide +kernel
def cuts46005 : List PrefixCut := [⟨42,175212098,175212200⟩,
⟨64,268554904,268555059⟩]
theorem checked46005 : checkPrefixCuts (2^48) 6033899521 10 Manual.Count131072.C046005.packed 64 cuts46005 = true := by
 decide +kernel
def pointBounds46005 : List (Nat × Nat × Nat) := [(6033985536,110618805895396,110619192423756)]
theorem point_links_checked46005 : (cuts46005.take 1).map (fun c => (6033899521-1+2*2^10*c.k,110618630683298+c.lower,110619017211556+c.upper)) = pointBounds46005 := by
 decide +kernel
def cuts46006 : List PrefixCut := [⟨64,268595755,268595913⟩]
theorem checked46006 : checkPrefixCuts (2^48) 6034030593 10 Manual.Count131072.C046006.packed 64 cuts46006 = true := by
 decide +kernel
def cuts46007 : List PrefixCut := [⟨7,29620741,29620758⟩,
⟨64,271015505,271015660⟩]
theorem checked46007 : checkPrefixCuts (2^48) 6034161665 10 Manual.Count131072.C046007.packed 64 cuts46007 = true := by
 decide +kernel
def pointBounds46007 : List (Nat × Nat × Nat) := [(6034176000,110619197454698,110619583983286)]
theorem point_links_checked46007 : (cuts46007.take 1).map (fun c => (6034161665-1+2*2^10*c.k,110619167833957+c.lower,110619554362528+c.upper)) = pointBounds46007 := by
 decide +kernel
def cuts46008 : List PrefixCut := [⟨36,151551529,151551614⟩,
⟨64,267651154,267651305⟩]
theorem checked46008 : checkPrefixCuts (2^48) 6034292737 10 Manual.Count131072.C046008.packed 64 cuts46008 = true := by
 decide +kernel
def pointBounds46008 : List (Nat × Nat × Nat) := [(6034366464,110619590400991,110619976929802)]
theorem point_links_checked46008 : (cuts46008.take 1).map (fun c => (6034292737-1+2*2^10*c.k,110619438849462+c.lower,110619825378188+c.upper)) = pointBounds46008 := by
 decide +kernel
def cuts46009 : List PrefixCut := [⟨64,270210795,270210952⟩]
theorem checked46009 : checkPrefixCuts (2^48) 6034423809 10 Manual.Count131072.C046009.packed 64 cuts46009 = true := by
 decide +kernel
def cuts46010 : List PrefixCut := [⟨1,3731508,3731510⟩,
⟨64,269085458,269085614⟩]
theorem checked46010 : checkPrefixCuts (2^48) 6034554881 10 Manual.Count131072.C046010.packed 64 cuts46010 = true := by
 decide +kernel
def pointBounds46010 : List (Nat × Nat × Nat) := [(6034556928,110619980442919,110620366971955)]
theorem point_links_checked46010 : (cuts46010.take 1).map (fun c => (6034554881-1+2*2^10*c.k,110619976711411+c.lower,110620363240445+c.upper)) = pointBounds46010 := by
 decide +kernel
def cuts46011 : List PrefixCut := [⟨30,127567516,127567595⟩,
⟨64,270152403,270152564⟩]
theorem checked46011 : checkPrefixCuts (2^48) 6034685953 10 Manual.Count131072.C046011.packed 64 cuts46011 = true := by
 decide +kernel
def pointBounds46011 : List (Nat × Nat × Nat) := [(6034747392,110620373364385,110620759893654)]
theorem point_links_checked46011 : (cuts46011.take 1).map (fun c => (6034685953-1+2*2^10*c.k,110620245796869+c.lower,110620632326059+c.upper)) = pointBounds46011 := by
 decide +kernel
def cuts46012 : List PrefixCut := [⟨59,252796158,252796313⟩,
⟨64,274344233,274344399⟩]
theorem checked46012 : checkPrefixCuts (2^48) 6034817025 10 Manual.Count131072.C046012.packed 64 cuts46012 = true := by
 decide +kernel
def pointBounds46012 : List (Nat × Nat × Nat) := [(6034937856,110620768745430,110621155274936)]
theorem point_links_checked46012 : (cuts46012.take 1).map (fun c => (6034817025-1+2*2^10*c.k,110620515949272+c.lower,110620902478623+c.upper)) = pointBounds46012 := by
 decide +kernel
def cuts46013 : List PrefixCut := [⟨64,270187274,270187433⟩]
theorem checked46013 : checkPrefixCuts (2^48) 6034948097 10 Manual.Count131072.C046013.packed 64 cuts46013 = true := by
 decide +kernel
def cuts46014 : List PrefixCut := [⟨24,102886983,102887039⟩,
⟨64,275078559,275078714⟩]
theorem checked46014 : checkPrefixCuts (2^48) 6035079169 10 Manual.Count131072.C046014.packed 64 cuts46014 = true := by
 decide +kernel
def pointBounds46014 : List (Nat × Nat × Nat) := [(6035128320,110621163367762,110621549897494)]
theorem point_links_checked46014 : (cuts46014.take 1).map (fun c => (6035079169-1+2*2^10*c.k,110621060480779+c.lower,110621447010455+c.upper)) = pointBounds46014 := by
 decide +kernel
def cuts46015 : List PrefixCut := [⟨53,225216693,225216815⟩,
⟨64,270362144,270362293⟩]
theorem checked46015 : checkPrefixCuts (2^48) 6035210241 10 Manual.Count131072.C046015.packed 64 cuts46015 = true := by
 decide +kernel
def pointBounds46015 : List (Nat × Nat × Nat) := [(6035318784,110621560776031,110621947305984)]
theorem point_links_checked46015 : (cuts46015.take 1).map (fun c => (6035210241-1+2*2^10*c.k,110621335559338+c.lower,110621722089169+c.upper)) = pointBounds46015 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000187
