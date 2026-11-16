import PlattAssemblyKernel
import PlattCertificates.Count131072.C042976
import PlattCertificates.Count131072.C042977
import PlattCertificates.Count131072.C042978
import PlattCertificates.Count131072.C042979
import PlattCertificates.Count131072.C042980
import PlattCertificates.Count131072.C042981
import PlattCertificates.Count131072.C042982
import PlattCertificates.Count131072.C042983
import PlattCertificates.Count131072.C042984
import PlattCertificates.Count131072.C042985
import PlattCertificates.Count131072.C042986
import PlattCertificates.Count131072.C042987
import PlattCertificates.Count131072.C042988
import PlattCertificates.Count131072.C042989
import PlattCertificates.Count131072.C042990
import PlattCertificates.Count131072.C042991
import PlattCertificates.Count131072.C042992
import PlattCertificates.Count131072.C042993
import PlattCertificates.Count131072.C042994
import PlattCertificates.Count131072.C042995
import PlattCertificates.Count131072.C042996
import PlattCertificates.Count131072.C042997
import PlattCertificates.Count131072.C042998
import PlattCertificates.Count131072.C042999
import PlattCertificates.Count131072.C043000
import PlattCertificates.Count131072.C043001
import PlattCertificates.Count131072.C043002
import PlattCertificates.Count131072.C043003
import PlattCertificates.Count131072.C043004
import PlattCertificates.Count131072.C043005
import PlattCertificates.Count131072.C043006
import PlattCertificates.Count131072.C043007
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000093
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts42976 : List PrefixCut := [⟨18,83190601,83190646⟩,
⟨64,291264554,291264722⟩]
theorem checked42976 : checkPrefixCuts (2^48) 5636882433 10 Manual.Count131072.C042976.packed 64 cuts42976 = true := by
 decide +kernel
def pointBounds42976 : List (Nat × Nat × Nat) := [(5636919296,109766751423847,109767137459241)]
theorem point_links_checked42976 : (cuts42976.take 1).map (fun c => (5636882433-1+2*2^10*c.k,109766668233246+c.lower,109767054268595+c.upper)) = pointBounds42976 := by
 decide +kernel
def cuts42977 : List PrefixCut := [⟨41,189395744,189395856⟩,
⟨64,295701791,295701966⟩]
theorem checked42977 : checkPrefixCuts (2^48) 5637013505 10 Manual.Count131072.C042977.packed 64 cuts42977 = true := by
 decide +kernel
def pointBounds42977 : List (Nat × Nat × Nat) := [(5637097472,109767148893544,109767534929173)]
theorem point_links_checked42977 : (cuts42977.take 1).map (fun c => (5637013505-1+2*2^10*c.k,109766959497800+c.lower,109767345533317+c.upper)) = pointBounds42977 := by
 decide +kernel
def cuts42978 : List PrefixCut := [⟨64,286407617,286407785⟩]
theorem checked42978 : checkPrefixCuts (2^48) 5637144577 10 Manual.Count131072.C042978.packed 64 cuts42978 = true := by
 decide +kernel
def pointBounds42978 : List (Nat × Nat × Nat) := [(5637275648,109767541607208,109767927643068)]
theorem point_links_checked42978 : (cuts42978.take 1).map (fun c => (5637144577-1+2*2^10*c.k,109767255199591+c.lower,109767641235283+c.upper)) = pointBounds42978 := by
 decide +kernel
def cuts42979 : List PrefixCut := [⟨64,292941861,292942031⟩]
theorem checked42979 : checkPrefixCuts (2^48) 5637275649 10 Manual.Count131072.C042979.packed 64 cuts42979 = true := by
 decide +kernel
def cuts42980 : List PrefixCut := [⟨23,104802328,104802387⟩,
⟨64,288491364,288491532⟩]
theorem checked42980 : checkPrefixCuts (2^48) 5637406721 10 Manual.Count131072.C042980.packed 64 cuts42980 = true := by
 decide +kernel
def pointBounds42980 : List (Nat × Nat × Nat) := [(5637453824,109767939351397,109768325387486)]
theorem point_links_checked42980 : (cuts42980.take 1).map (fun c => (5637406721-1+2*2^10*c.k,109767834549069+c.lower,109768220585099+c.upper)) = pointBounds42980 := by
 decide +kernel
def cuts42981 : List PrefixCut := [⟨46,208051101,208051218⟩,
⟨64,288534547,288534707⟩]
theorem checked42981 : checkPrefixCuts (2^48) 5637537793 10 Manual.Count131072.C042981.packed 64 cuts42981 = true := by
 decide +kernel
def pointBounds42981 : List (Nat × Nat × Nat) := [(5637632000,109768331091534,109768717127849)]
theorem point_links_checked42981 : (cuts42981.take 1).map (fun c => (5637537793-1+2*2^10*c.k,109768123040433+c.lower,109768509076631+c.upper)) = pointBounds42981 := by
 decide +kernel
def cuts42982 : List PrefixCut := [⟨64,290474990,290475163⟩]
theorem checked42982 : checkPrefixCuts (2^48) 5637668865 10 Manual.Count131072.C042982.packed 64 cuts42982 = true := by
 decide +kernel
def cuts42983 : List PrefixCut := [⟨5,21917657,21917669⟩,
⟨64,286424283,286424451⟩]
theorem checked42983 : checkPrefixCuts (2^48) 5637799937 10 Manual.Count131072.C042983.packed 64 cuts42983 = true := by
 decide +kernel
def pointBounds42983 : List (Nat × Nat × Nat) := [(5637810176,109768723967627,109769110004170)]
theorem point_links_checked42983 : (cuts42983.take 1).map (fun c => (5637799937-1+2*2^10*c.k,109768702049970+c.lower,109769088086501+c.upper)) = pointBounds42983 := by
 decide +kernel
def cuts42984 : List PrefixCut := [⟨28,125661125,125661195⟩,
⟨64,294056042,294056209⟩]
theorem checked42984 : checkPrefixCuts (2^48) 5637931009 10 Manual.Count131072.C042984.packed 64 cuts42984 = true := by
 decide +kernel
def pointBounds42984 : List (Nat × Nat × Nat) := [(5637988352,109769114135378,109769500172147)]
theorem point_links_checked42984 : (cuts42984.take 1).map (fun c => (5637931009-1+2*2^10*c.k,109768988474253+c.lower,109769374510952+c.upper)) = pointBounds42984 := by
 decide +kernel
def cuts42985 : List PrefixCut := [⟨51,232444212,232444350⟩,
⟨64,291602975,291603146⟩]
theorem checked42985 : checkPrefixCuts (2^48) 5638062081 10 Manual.Count131072.C042985.packed 64 cuts42985 = true := by
 decide +kernel
def pointBounds42985 : List (Nat × Nat × Nat) := [(5638166528,109769514974507,109769901011511)]
theorem point_links_checked42985 : (cuts42985.take 1).map (fun c => (5638062081-1+2*2^10*c.k,109769282530295+c.lower,109769668567161+c.upper)) = pointBounds42985 := by
 decide +kernel
def cuts42986 : List PrefixCut := [⟨64,290797453,290797620⟩]
theorem checked42986 : checkPrefixCuts (2^48) 5638193153 10 Manual.Count131072.C042986.packed 64 cuts42986 = true := by
 decide +kernel
def cuts42987 : List PrefixCut := [⟨10,45229004,45229030⟩,
⟨64,295633031,295633197⟩]
theorem checked42987 : checkPrefixCuts (2^48) 5638324225 10 Manual.Count131072.C042987.packed 64 cuts42987 = true := by
 decide +kernel
def pointBounds42987 : List (Nat × Nat × Nat) := [(5638344704,109769910159727,109770296196957)]
theorem point_links_checked42987 : (cuts42987.take 1).map (fun c => (5638324225-1+2*2^10*c.k,109769864930723+c.lower,109770250967927+c.upper)) = pointBounds42987 := by
 decide +kernel
def cuts42988 : List PrefixCut := [⟨33,152606251,152606340⟩,
⟨64,294328244,294328417⟩]
theorem checked42988 : checkPrefixCuts (2^48) 5638455297 10 Manual.Count131072.C042988.packed 64 cuts42988 = true := by
 decide +kernel
def pointBounds42988 : List (Nat × Nat × Nat) := [(5638522880,109770313170005,109770699207464)]
theorem point_links_checked42988 : (cuts42988.take 1).map (fun c => (5638455297-1+2*2^10*c.k,109770160563754+c.lower,109770546601124+c.upper)) = pointBounds42988 := by
 decide +kernel
def cuts42989 : List PrefixCut := [⟨56,253488176,253488322⟩,
⟨64,289778794,289778961⟩]
theorem checked42989 : checkPrefixCuts (2^48) 5638586369 10 Manual.Count131072.C042989.packed 64 cuts42989 = true := by
 decide +kernel
def pointBounds42989 : List (Nat × Nat × Nat) := [(5638701056,109770708380174,109771094417863)]
theorem point_links_checked42989 : (cuts42989.take 1).map (fun c => (5638586369-1+2*2^10*c.k,109770454891998+c.lower,109770840929541+c.upper)) = pointBounds42989 := by
 decide +kernel
def cuts42990 : List PrefixCut := [⟨64,292068284,292068452⟩]
theorem checked42990 : checkPrefixCuts (2^48) 5638717441 10 Manual.Count131072.C042990.packed 64 cuts42990 = true := by
 decide +kernel
def cuts42991 : List PrefixCut := [⟨15,68486058,68486097⟩,
⟨64,292560648,292560817⟩]
theorem checked42991 : checkPrefixCuts (2^48) 5638848513 10 Manual.Count131072.C042991.packed 64 cuts42991 = true := by
 decide +kernel
def pointBounds42991 : List (Nat × Nat × Nat) := [(5638879232,109771105225134,109771491263051)]
theorem point_links_checked42991 : (cuts42991.take 1).map (fun c => (5638848513-1+2*2^10*c.k,109771036739076+c.lower,109771422776954+c.upper)) = pointBounds42991 := by
 decide +kernel
def cuts42992 : List PrefixCut := [⟨38,172458346,172458445⟩,
⟨64,289608856,289609024⟩]
theorem checked42992 : checkPrefixCuts (2^48) 5638979585 10 Manual.Count131072.C042992.packed 64 cuts42992 = true := by
 decide +kernel
def pointBounds42992 : List (Nat × Nat × Nat) := [(5639057408,109771501758070,109771887796216)]
theorem point_links_checked42992 : (cuts42992.take 1).map (fun c => (5638979585-1+2*2^10*c.k,109771329299724+c.lower,109771715337771+c.upper)) = pointBounds42992 := by
 decide +kernel
def cuts42993 : List PrefixCut := [⟨61,281416333,281416489⟩,
⟨64,295442064,295442228⟩]
theorem checked42993 : checkPrefixCuts (2^48) 5639110657 10 Manual.Count131072.C042993.packed 64 cuts42993 = true := by
 decide +kernel
def pointBounds42993 : List (Nat × Nat × Nat) := [(5639235584,109771900324913,109772286363284)]
theorem point_links_checked42993 : (cuts42993.take 1).map (fun c => (5639110657-1+2*2^10*c.k,109771618908580+c.lower,109772004946795+c.upper)) = pointBounds42993 := by
 decide +kernel
def cuts42994 : List PrefixCut := [⟨64,290393978,290394151⟩]
theorem checked42994 : checkPrefixCuts (2^48) 5639241729 10 Manual.Count131072.C042994.packed 64 cuts42994 = true := by
 decide +kernel
def cuts42995 : List PrefixCut := [⟨20,93884970,93885021⟩,
⟨64,291784812,291784981⟩]
theorem checked42995 : checkPrefixCuts (2^48) 5639372801 10 Manual.Count131072.C042995.packed 64 cuts42995 = true := by
 decide +kernel
def pointBounds42995 : List (Nat × Nat × Nat) := [(5639413760,109772298629592,109772684668195)]
theorem point_links_checked42995 : (cuts42995.take 1).map (fun c => (5639372801-1+2*2^10*c.k,109772204744622+c.lower,109772590783174+c.upper)) = pointBounds42995 := by
 decide +kernel
def cuts42996 : List PrefixCut := [⟨43,197148058,197148171⟩,
⟨64,292676408,292676579⟩]
theorem checked42996 : checkPrefixCuts (2^48) 5639503873 10 Manual.Count131072.C042996.packed 64 cuts42996 = true := by
 decide +kernel
def pointBounds42996 : List (Nat × Nat × Nat) := [(5639591936,109772693677492,109773079716326)]
theorem point_links_checked42996 : (cuts42996.take 1).map (fun c => (5639503873-1+2*2^10*c.k,109772496529434+c.lower,109772882568155+c.upper)) = pointBounds42996 := by
 decide +kernel
def cuts42997 : List PrefixCut := [⟨64,291371932,291372099⟩]
theorem checked42997 : checkPrefixCuts (2^48) 5639634945 10 Manual.Count131072.C042997.packed 64 cuts42997 = true := by
 decide +kernel
def cuts42998 : List PrefixCut := [⟨2,9682336,9682342⟩,
⟨64,294758938,294759110⟩]
theorem checked42998 : checkPrefixCuts (2^48) 5639766017 10 Manual.Count131072.C042998.packed 64 cuts42998 = true := by
 decide +kernel
def pointBounds42998 : List (Nat × Nat × Nat) := [(5639770112,109773090260110,109773476299175)]
theorem point_links_checked42998 : (cuts42998.take 1).map (fun c => (5639766017-1+2*2^10*c.k,109773080577774+c.lower,109773466616833+c.upper)) = pointBounds42998 := by
 decide +kernel
def cuts42999 : List PrefixCut := [⟨25,113539741,113539807⟩,
⟨64,290210526,290210695⟩]
theorem checked42999 : checkPrefixCuts (2^48) 5639897089 10 Manual.Count131072.C042999.packed 64 cuts42999 = true := by
 decide +kernel
def pointBounds42999 : List (Nat × Nat × Nat) := [(5639948288,109773488876453,109773874915750)]
theorem point_links_checked42999 : (cuts42999.take 1).map (fun c => (5639897089-1+2*2^10*c.k,109773375336712+c.lower,109773761375943+c.upper)) = pointBounds42999 := by
 decide +kernel
def cuts43000 : List PrefixCut := [⟨48,214646628,214646751⟩,
⟨64,289205643,289205810⟩]
theorem checked43000 : checkPrefixCuts (2^48) 5640028161 10 Manual.Count131072.C043000.packed 64 cuts43000 = true := by
 decide +kernel
def pointBounds43000 : List (Nat × Nat × Nat) := [(5640126464,109773880193866,109774266233389)]
theorem point_links_checked43000 : (cuts43000.take 1).map (fun c => (5640028161-1+2*2^10*c.k,109773665547238+c.lower,109774051586638+c.upper)) = pointBounds43000 := by
 decide +kernel
def cuts43001 : List PrefixCut := [⟨64,291893818,291893992⟩]
theorem checked43001 : checkPrefixCuts (2^48) 5640159233 10 Manual.Count131072.C043001.packed 64 cuts43001 = true := by
 decide +kernel
def cuts43002 : List PrefixCut := [⟨7,31838923,31838940⟩,
⟨64,294731540,294731712⟩]
theorem checked43002 : checkPrefixCuts (2^48) 5640290305 10 Manual.Count131072.C043002.packed 64 cuts43002 = true := by
 decide +kernel
def pointBounds43002 : List (Nat × Nat × Nat) := [(5640304640,109774278485622,109774664525380)]
theorem point_links_checked43002 : (cuts43002.take 1).map (fun c => (5640290305-1+2*2^10*c.k,109774246646699+c.lower,109774632686440+c.upper)) = pointBounds43002 := by
 decide +kernel
def cuts43003 : List PrefixCut := [⟨30,138480528,138480607⟩,
⟨64,291830350,291830516⟩]
theorem checked43003 : checkPrefixCuts (2^48) 5640421377 10 Manual.Count131072.C043003.packed 64 cuts43003 = true := by
 decide +kernel
def pointBounds43003 : List (Nat × Nat × Nat) := [(5640482816,109774679858767,109775065898759)]
theorem point_links_checked43003 : (cuts43003.take 1).map (fun c => (5640421377-1+2*2^10*c.k,109774541378239+c.lower,109774927418152+c.upper)) = pointBounds43003 := by
 decide +kernel
def cuts43004 : List PrefixCut := [⟨53,240575294,240575436⟩,
⟨64,291374456,291374629⟩]
theorem checked43004 : checkPrefixCuts (2^48) 5640552449 10 Manual.Count131072.C043004.packed 64 cuts43004 = true := by
 decide +kernel
def pointBounds43004 : List (Nat × Nat × Nat) := [(5640660992,109775073783883,109775459824104)]
theorem point_links_checked43004 : (cuts43004.take 1).map (fun c => (5640552449-1+2*2^10*c.k,109774833208589+c.lower,109775219248668+c.upper)) = pointBounds43004 := by
 decide +kernel
def cuts43005 : List PrefixCut := [⟨64,294311762,294311934⟩]
theorem checked43005 : checkPrefixCuts (2^48) 5640683521 10 Manual.Count131072.C043005.packed 64 cuts43005 = true := by
 decide +kernel
def cuts43006 : List PrefixCut := [⟨12,54590142,54590172⟩,
⟨64,290412818,290412986⟩]
theorem checked43006 : checkPrefixCuts (2^48) 5640814593 10 Manual.Count131072.C043006.packed 64 cuts43006 = true := by
 decide +kernel
def pointBounds43006 : List (Nat × Nat × Nat) := [(5640839168,109775473484949,109775859525403)]
theorem point_links_checked43006 : (cuts43006.take 1).map (fun c => (5640814593-1+2*2^10*c.k,109775418894807+c.lower,109775804935231+c.upper)) = pointBounds43006 := by
 decide +kernel
def cuts43007 : List PrefixCut := [⟨35,158476729,158476818⟩,
⟨64,289008931,289009095⟩]
theorem checked43007 : checkPrefixCuts (2^48) 5640945665 10 Manual.Count131072.C043007.packed 64 cuts43007 = true := by
 decide +kernel
def pointBounds43007 : List (Nat × Nat × Nat) := [(5641017344,109775867784354,109776253825035)]
theorem point_links_checked43007 : (cuts43007.take 1).map (fun c => (5640945665-1+2*2^10*c.k,109775709307625+c.lower,109776095348217+c.upper)) = pointBounds43007 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000093
