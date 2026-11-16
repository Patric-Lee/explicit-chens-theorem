import PlattAssemblyKernel
import PlattCertificates.Count131072.C020640
import PlattCertificates.Count131072.C020641
import PlattCertificates.Count131072.C020642
import PlattCertificates.Count131072.C020643
import PlattCertificates.Count131072.C020644
import PlattCertificates.Count131072.C020645
import PlattCertificates.Count131072.C020646
import PlattCertificates.Count131072.C020647
import PlattCertificates.Count131072.C020648
import PlattCertificates.Count131072.C020649
import PlattCertificates.Count131072.C020650
import PlattCertificates.Count131072.C020651
import PlattCertificates.Count131072.C020652
import PlattCertificates.Count131072.C020653
import PlattCertificates.Count131072.C020654
import PlattCertificates.Count131072.C020655
import PlattCertificates.Count131072.C020656
import PlattCertificates.Count131072.C020657
import PlattCertificates.Count131072.C020658
import PlattCertificates.Count131072.C020659
import PlattCertificates.Count131072.C020660
import PlattCertificates.Count131072.C020661
import PlattCertificates.Count131072.C020662
import PlattCertificates.Count131072.C020663
import PlattCertificates.Count131072.C020664
import PlattCertificates.Count131072.C020665
import PlattCertificates.Count131072.C020666
import PlattCertificates.Count131072.C020667
import PlattCertificates.Count131072.C020668
import PlattCertificates.Count131072.C020669
import PlattCertificates.Count131072.C020670
import PlattCertificates.Count131072.C020671
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000020
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts20640 : List PrefixCut := [⟨5,25142255,25142270⟩,
⟨88,425126018,425126268⟩,
⟨128,620126559,620126923⟩]
theorem checked20640 : checkPrefixCuts (2^48) 2709258241 9 Manual.Count131072.C020640.packed 128 cuts20640 = true := by
 decide +kernel
def pointBounds20640 : List (Nat × Nat × Nat) := [(2709263360,100428768568357,100429149176747),(2709348352,100429168552120,100429549160745)]
theorem point_links_checked20640 : (cuts20640.take 2).map (fun c => (2709258241-1+2*2^9*c.k,100428743426102+c.lower,100429124034477+c.upper)) = pointBounds20640 := by
 decide +kernel
def cuts20641 : List PrefixCut := [⟨43,211723414,211723535⟩,
⟨126,613967531,613967890⟩,
⟨128,624252017,624252382⟩]
theorem checked20641 : checkPrefixCuts (2^48) 2709389313 9 Manual.Count131072.C020641.packed 128 cuts20641 = true := by
 decide +kernel
def pointBounds20641 : List (Nat × Nat × Nat) := [(2709433344,100429575276075,100429955884935),(2709518336,100429977520192,100430358129290)]
theorem point_links_checked20641 : (cuts20641.take 2).map (fun c => (2709389313-1+2*2^9*c.k,100429363552661+c.lower,100429744161400+c.upper)) = pointBounds20641 := by
 decide +kernel
def cuts20642 : List PrefixCut := [⟨81,405867243,405867472⟩,
⟨128,631909150,631909514⟩]
theorem checked20642 : checkPrefixCuts (2^48) 2709520385 9 Manual.Count131072.C020642.packed 128 cuts20642 = true := by
 decide +kernel
def pointBounds20642 : List (Nat × Nat × Nat) := [(2709603328,100430393671921,100430774281254)]
theorem point_links_checked20642 : (cuts20642.take 1).map (fun c => (2709520385-1+2*2^9*c.k,100429987804678+c.lower,100430368413782+c.upper)) = pointBounds20642 := by
 decide +kernel
def cuts20643 : List PrefixCut := [⟨36,172852865,172852965⟩,
⟨119,582953712,582954048⟩,
⟨128,624710972,624711333⟩]
theorem checked20643 : checkPrefixCuts (2^48) 2709651457 9 Manual.Count131072.C020643.packed 128 cuts20643 = true := by
 decide +kernel
def pointBounds20643 : List (Nat × Nat × Nat) := [(2709688320,100430792566693,100431173176261),(2709773312,100431202667540,100431583277344)]
theorem point_links_checked20643 : (cuts20643.take 2).map (fun c => (2709651457-1+2*2^9*c.k,100430619713828+c.lower,100431000323296+c.upper)) = pointBounds20643 := by
 decide +kernel
def cuts20644 : List PrefixCut := [⟨74,369369371,369369579⟩,
⟨128,629043523,629043875⟩]
theorem checked20644 : checkPrefixCuts (2^48) 2709782529 9 Manual.Count131072.C020644.packed 128 cuts20644 = true := by
 decide +kernel
def pointBounds20644 : List (Nat × Nat × Nat) := [(2709858304,100431613794171,100431994404208)]
theorem point_links_checked20644 : (cuts20644.take 1).map (fun c => (2709782529-1+2*2^9*c.k,100431244424800+c.lower,100431625034629+c.upper)) = pointBounds20644 := by
 decide +kernel
def cuts20645 : List PrefixCut := [⟨29,142818518,142818603⟩,
⟨112,545506368,545506691⟩,
⟨128,620599950,620600317⟩]
theorem checked20645 : checkPrefixCuts (2^48) 2709913601 9 Manual.Count131072.C020645.packed 128 cuts20645 = true := by
 decide +kernel
def pointBounds20645 : List (Nat × Nat × Nat) := [(2709943296,100432016286841,100432396897107),(2710028288,100432418974691,100432799585195)]
theorem point_links_checked20645 : (cuts20645.take 2).map (fun c => (2709913601-1+2*2^9*c.k,100431873468323+c.lower,100432254078504+c.upper)) = pointBounds20645 := by
 decide +kernel
def cuts20646 : List PrefixCut := [⟨67,329035604,329035788⟩,
⟨128,632513784,632514139⟩]
theorem checked20646 : checkPrefixCuts (2^48) 2710044673 9 Manual.Count131072.C020646.packed 128 cuts20646 = true := by
 decide +kernel
def pointBounds20646 : List (Nat × Nat × Nat) := [(2710113280,100432823103877,100433203714609)]
theorem point_links_checked20646 : (cuts20646.take 1).map (fun c => (2710044673-1+2*2^9*c.k,100432494068273+c.lower,100432874678821+c.upper)) = pointBounds20646 := by
 decide +kernel
def cuts20647 : List PrefixCut := [⟨22,106766131,106766192⟩,
⟨105,513362573,513362871⟩,
⟨128,632379220,632379590⟩]
theorem checked20647 : checkPrefixCuts (2^48) 2710175745 9 Manual.Count131072.C020647.packed 128 cuts20647 = true := by
 decide +kernel
def pointBounds20647 : List (Nat × Nat × Nat) := [(2710198272,100433233348188,100433613959152),(2710283264,100433639944630,100434020555831)]
theorem point_links_checked20647 : (cuts20647.take 2).map (fun c => (2710175745-1+2*2^9*c.k,100433126582057+c.lower,100433507192960+c.upper)) = pointBounds20647 := by
 decide +kernel
def cuts20648 : List PrefixCut := [⟨60,294421365,294421538⟩,
⟨128,629337066,629337427⟩]
theorem checked20648 : checkPrefixCuts (2^48) 2710306817 9 Manual.Count131072.C020648.packed 128 cuts20648 = true := by
 decide +kernel
def pointBounds20648 : List (Nat × Nat × Nat) := [(2710368256,100434053382642,100434433994088)]
theorem point_links_checked20648 : (cuts20648.take 1).map (fun c => (2710306817-1+2*2^9*c.k,100433758961277+c.lower,100434139572550+c.upper)) = pointBounds20648 := by
 decide +kernel
def cuts20649 : List PrefixCut := [⟨15,74043765,74043809⟩,
⟨98,478421162,478421445⟩,
⟨128,624841269,624841635⟩]
theorem checked20649 : checkPrefixCuts (2^48) 2710437889 9 Manual.Count131072.C020649.packed 128 cuts20649 = true := by
 decide +kernel
def pointBounds20649 : List (Nat × Nat × Nat) := [(2710453248,100434462342108,100434842953786),(2710538240,100434866719505,100435247331422)]
theorem point_links_checked20649 : (cuts20649.take 2).map (fun c => (2710437889-1+2*2^9*c.k,100434388298343+c.lower,100434768909977+c.upper)) = pointBounds20649 := by
 decide +kernel
def cuts20650 : List PrefixCut := [⟨53,252856339,252856487⟩,
⟨128,621799615,621799979⟩]
theorem checked20650 : checkPrefixCuts (2^48) 2710568961 9 Manual.Count131072.C020650.packed 128 cuts20650 = true := by
 decide +kernel
def pointBounds20650 : List (Nat × Nat × Nat) := [(2710623232,100435265995951,100435646608099)]
theorem point_links_checked20650 : (cuts20650.take 1).map (fun c => (2710568961-1+2*2^9*c.k,100435013139612+c.lower,100435393751612+c.upper)) = pointBounds20650 := by
 decide +kernel
def cuts20651 : List PrefixCut := [⟨8,41950673,41950697⟩,
⟨91,447951448,447951710⟩,
⟨128,623950350,623950715⟩]
theorem checked20651 : checkPrefixCuts (2^48) 2710700033 9 Manual.Count131072.C020651.packed 128 cuts20651 = true := by
 decide +kernel
def pointBounds20651 : List (Nat × Nat × Nat) := [(2710708224,100435676889900,100436057502288),(2710793216,100436082890675,100436463503301)]
theorem point_links_checked20651 : (cuts20651.take 2).map (fun c => (2710700033-1+2*2^9*c.k,100435634939227+c.lower,100436015551591+c.upper)) = pointBounds20651 := by
 decide +kernel
def cuts20652 : List PrefixCut := [⟨46,222928442,222928572⟩,
⟨128,626619722,626620088⟩]
theorem checked20652 : checkPrefixCuts (2^48) 2710831105 9 Manual.Count131072.C020652.packed 128 cuts20652 = true := by
 decide +kernel
def pointBounds20652 : List (Nat × Nat × Nat) := [(2710878208,100436481818019,100436862430878)]
theorem point_links_checked20652 : (cuts20652.take 1).map (fun c => (2710831105-1+2*2^9*c.k,100436258889577+c.lower,100436639502306+c.upper)) = pointBounds20652 := by
 decide +kernel
def cuts20653 : List PrefixCut := [⟨1,4360792,4360795⟩,
⟨84,407104707,407104944⟩,
⟨128,623059155,623059518⟩]
theorem checked20653 : checkPrefixCuts (2^48) 2710962177 9 Manual.Count131072.C020653.packed 128 cuts20653 = true := by
 decide +kernel
def pointBounds20653 : List (Nat × Nat × Nat) := [(2710963200,100436889870091,100437270483189),(2711048192,100437292614006,100437673227338)]
theorem point_links_checked20653 : (cuts20653.take 2).map (fun c => (2710962177-1+2*2^9*c.k,100436885509299+c.lower,100437266122394+c.upper)) = pointBounds20653 := by
 decide +kernel
def cuts20654 : List PrefixCut := [⟨39,189268613,189268723⟩,
⟨122,594375157,594375500⟩,
⟨128,625728338,625728701⟩]
theorem checked20654 : checkPrefixCuts (2^48) 2711093249 9 Manual.Count131072.C020654.packed 128 cuts20654 = true := by
 decide +kernel
def pointBounds20654 : List (Nat × Nat × Nat) := [(2711133184,100437697837067,100438078450635),(2711218176,100438102943611,100438483557412)]
theorem point_links_checked20654 : (cuts20654.take 2).map (fun c => (2711093249-1+2*2^9*c.k,100437508568454+c.lower,100437889181912+c.upper)) = pointBounds20654 := by
 decide +kernel
def cuts20655 : List PrefixCut := [⟨77,379346766,379346990⟩,
⟨128,630992752,630993121⟩]
theorem checked20655 : checkPrefixCuts (2^48) 2711224321 9 Manual.Count131072.C020655.packed 128 cuts20655 = true := by
 decide +kernel
def pointBounds20655 : List (Nat × Nat × Nat) := [(2711303168,100438513643558,100438894257603)]
theorem point_links_checked20655 : (cuts20655.take 1).map (fun c => (2711224321-1+2*2^9*c.k,100438134296792+c.lower,100438514910613+c.upper)) = pointBounds20655 := by
 decide +kernel
def cuts20656 : List PrefixCut := [⟨32,154369511,154369598⟩,
⟨115,563382727,563383048⟩,
⟨128,629197373,629197731⟩]
theorem checked20656 : checkPrefixCuts (2^48) 2711355393 9 Manual.Count131072.C020656.packed 128 cuts20656 = true := by
 decide +kernel
def pointBounds20656 : List (Nat × Nat × Nat) := [(2711388160,100438919659055,100439300273332),(2711473152,100439328672271,100439709286782)]
theorem point_links_checked20656 : (cuts20656.take 2).map (fun c => (2711355393-1+2*2^9*c.k,100438765289544+c.lower,100439145903734+c.upper)) = pointBounds20656 := by
 decide +kernel
def cuts20657 : List PrefixCut := [⟨70,352943658,352943857⟩,
⟨128,638094486,638094848⟩]
theorem checked20657 : checkPrefixCuts (2^48) 2711486465 9 Manual.Count131072.C020657.packed 128 cuts20657 = true := by
 decide +kernel
def pointBounds20657 : List (Nat × Nat × Nat) := [(2711558144,100439747430575,100440128045322)]
theorem point_links_checked20657 : (cuts20657.take 1).map (fun c => (2711486465-1+2*2^9*c.k,100439394486917+c.lower,100439775101465+c.upper)) = pointBounds20657 := by
 decide +kernel
def cuts20658 : List PrefixCut := [⟨25,119788461,119788533⟩,
⟨108,524715019,524715328⟩,
⟨128,621455408,621455773⟩]
theorem checked20658 : checkPrefixCuts (2^48) 2711617537 9 Manual.Count131072.C020658.packed 128 cuts20658 = true := by
 decide +kernel
def pointBounds20658 : List (Nat × Nat × Nat) := [(2711643136,100440152369864,100440532984846),(2711728128,100440557296422,100440937911641)]
theorem point_links_checked20658 : (cuts20658.take 2).map (fun c => (2711617537-1+2*2^9*c.k,100440032581403+c.lower,100440413196313+c.upper)) = pointBounds20658 := by
 decide +kernel
def cuts20659 : List PrefixCut := [⟨63,305993774,305993952⟩,
⟨128,621944385,621944741⟩]
theorem checked20659 : checkPrefixCuts (2^48) 2711748609 9 Manual.Count131072.C020659.packed 128 cuts20659 = true := by
 decide +kernel
def pointBounds20659 : List (Nat × Nat × Nat) := [(2711813120,100440960030585,100441340646038)]
theorem point_links_checked20659 : (cuts20659.take 1).map (fun c => (2711748609-1+2*2^9*c.k,100440654036811+c.lower,100441034652086+c.upper)) = pointBounds20659 := by
 decide +kernel
def cuts20660 : List PrefixCut := [⟨18,87912607,87912657⟩,
⟨101,499547550,499547836⟩,
⟨128,634784362,634784728⟩]
theorem checked20660 : checkPrefixCuts (2^48) 2711879681 9 Manual.Count131072.C020660.packed 128 cuts20660 = true := by
 decide +kernel
def pointBounds20660 : List (Nat × Nat × Nat) := [(2711898112,100441363893803,100441744509484),(2711983104,100441775528746,100442156144663)]
theorem point_links_checked20660 : (cuts20660.take 2).map (fun c => (2711879681-1+2*2^9*c.k,100441275981196+c.lower,100441656596827+c.upper)) = pointBounds20660 := by
 decide +kernel
def cuts20661 : List PrefixCut := [⟨56,272752664,272752820⟩,
⟨128,625828165,625828527⟩]
theorem checked20661 : checkPrefixCuts (2^48) 2712010753 9 Manual.Count131072.C020661.packed 128 cuts20661 = true := by
 decide +kernel
def pointBounds20661 : List (Nat × Nat × Nat) := [(2712068096,100442183518222,100442564134375)]
theorem point_links_checked20661 : (cuts20661.take 1).map (fun c => (2712010753-1+2*2^9*c.k,100441910765558+c.lower,100442291381555+c.upper)) = pointBounds20661 := by
 decide +kernel
def cuts20662 : List PrefixCut := [⟨11,52929348,52929379⟩,
⟨94,458506209,458506470⟩,
⟨128,626939358,626939714⟩]
theorem checked20662 : checkPrefixCuts (2^48) 2712141825 9 Manual.Count131072.C020662.packed 128 cuts20662 = true := by
 decide +kernel
def pointBounds20662 : List (Nat × Nat × Nat) := [(2712153088,100442589523071,100442970139461),(2712238080,100442995099932,100443375716552)]
theorem point_links_checked20662 : (cuts20662.take 2).map (fun c => (2712141825-1+2*2^9*c.k,100442536593723+c.lower,100442917210082+c.upper)) = pointBounds20662 := by
 decide +kernel
def cuts20663 : List PrefixCut := [⟨49,238791482,238791626⟩,
⟨128,628154412,628154784⟩]
theorem checked20663 : checkPrefixCuts (2^48) 2712272897 9 Manual.Count131072.C020663.packed 128 cuts20663 = true := by
 decide +kernel
def pointBounds20663 : List (Nat × Nat × Nat) := [(2712323072,100443402324563,100443782941422)]
theorem point_links_checked20663 : (cuts20663.take 1).map (fun c => (2712272897-1+2*2^9*c.k,100443163533081+c.lower,100443544149796+c.upper)) = pointBounds20663 := by
 decide +kernel
def cuts20664 : List PrefixCut := [⟨4,18782939,18782950⟩,
⟨87,420170841,420171093⟩,
⟨128,623869380,623869744⟩]
theorem checked20664 : checkPrefixCuts (2^48) 2712403969 9 Manual.Count131072.C020664.packed 128 cuts20664 = true := by
 decide +kernel
def pointBounds20664 : List (Nat × Nat × Nat) := [(2712408064,100443810470432,100444191087530),(2712493056,100444211858334,100444592475673)]
theorem point_links_checked20664 : (cuts20664.take 2).map (fun c => (2712403969-1+2*2^9*c.k,100443791687493+c.lower,100444172304580+c.upper)) = pointBounds20664 := by
 decide +kernel
def cuts20665 : List PrefixCut := [⟨42,200478575,200478691⟩,
⟨125,605369328,605369684⟩,
⟨128,620207473,620207838⟩]
theorem checked20665 : checkPrefixCuts (2^48) 2712535041 9 Manual.Count131072.C020665.packed 128 cuts20665 = true := by
 decide +kernel
def pointBounds20665 : List (Nat × Nat × Nat) := [(2712578048,100444616035448,100444996653015),(2712663040,100445020926201,100445401544008)]
theorem point_links_checked20665 : (cuts20665.take 2).map (fun c => (2712535041-1+2*2^9*c.k,100444415556873+c.lower,100444796174324+c.upper)) = pointBounds20665 := by
 decide +kernel
def cuts20666 : List PrefixCut := [⟨80,391700133,391700361⟩,
⟨128,625676921,625677288⟩]
theorem checked20666 : checkPrefixCuts (2^48) 2712666113 9 Manual.Count131072.C020666.packed 128 cuts20666 = true := by
 decide +kernel
def pointBounds20666 : List (Nat × Nat × Nat) := [(2712748032,100445427464479,100445808082523)]
theorem point_links_checked20666 : (cuts20666.take 1).map (fun c => (2712666113-1+2*2^9*c.k,100445035764346+c.lower,100445416382162+c.upper)) = pointBounds20666 := by
 decide +kernel
def cuts20667 : List PrefixCut := [⟨35,167775869,167775969⟩,
⟨118,582485344,582485689⟩,
⟨128,629278109,629278480⟩]
theorem checked20667 : checkPrefixCuts (2^48) 2712797185 9 Manual.Count131072.C020667.packed 128 cuts20667 = true := by
 decide +kernel
def pointBounds20667 : List (Nat × Nat × Nat) := [(2712833024,100445829217136,100446209835419),(2712918016,100446243926611,100446624545139)]
theorem point_links_checked20667 : (cuts20667.take 2).map (fun c => (2712797185-1+2*2^9*c.k,100445661441267+c.lower,100446042059450+c.upper)) = pointBounds20667 := by
 decide +kernel
def cuts20668 : List PrefixCut := [⟨73,359188586,359188798⟩,
⟨128,626031630,626031997⟩]
theorem checked20668 : checkPrefixCuts (2^48) 2712928257 9 Manual.Count131072.C020668.packed 128 cuts20668 = true := by
 decide +kernel
def pointBounds20668 : List (Nat × Nat × Nat) := [(2713003008,100446649907962,100447030526728)]
theorem point_links_checked20668 : (cuts20668.take 1).map (fun c => (2712928257-1+2*2^9*c.k,100446290719376+c.lower,100446671337930+c.upper)) = pointBounds20668 := by
 decide +kernel
def cuts20669 : List PrefixCut := [⟨28,137465565,137465648⟩,
⟨111,542591410,542591730⟩,
⟨128,621955165,621955532⟩]
theorem checked20669 : checkPrefixCuts (2^48) 2713059329 9 Manual.Count131072.C020669.packed 128 cuts20669 = true := by
 decide +kernel
def pointBounds20669 : List (Nat × Nat × Nat) := [(2713088000,100447054216571,100447434835575),(2713172992,100447459342416,100447839961657)]
theorem point_links_checked20669 : (cuts20669.take 2).map (fun c => (2713059329-1+2*2^9*c.k,100446916751006+c.lower,100447297369927+c.upper)) = pointBounds20669 := by
 decide +kernel
def cuts20670 : List PrefixCut := [⟨66,320043601,320043783⟩,
⟨128,627942018,627942380⟩]
theorem checked20670 : checkPrefixCuts (2^48) 2713190401 9 Manual.Count131072.C020670.packed 128 cuts20670 = true := by
 decide +kernel
def pointBounds20670 : List (Nat × Nat × Nat) := [(2713257984,100447858749772,100448239369242)]
theorem point_links_checked20670 : (cuts20670.take 1).map (fun c => (2713190401-1+2*2^9*c.k,100447538706171+c.lower,100447919325459+c.upper)) = pointBounds20670 := by
 decide +kernel
def cuts20671 : List PrefixCut := [⟨21,99588206,99588264⟩,
⟨104,513182387,513182684⟩,
⟨128,631646145,631646509⟩]
theorem checked20671 : checkPrefixCuts (2^48) 2713321473 9 Manual.Count131072.C020671.packed 128 cuts20671 = true := by
 decide +kernel
def pointBounds20671 : List (Nat × Nat × Nat) := [(2713342976,100448266236395,100448646856103),(2713427968,100448679830576,100449060450523)]
theorem point_links_checked20671 : (cuts20671.take 2).map (fun c => (2713321473-1+2*2^9*c.k,100448166648189+c.lower,100448547267839+c.upper)) = pointBounds20671 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000020
