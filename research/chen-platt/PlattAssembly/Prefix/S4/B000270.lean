import PlattAssemblyKernel
import PlattCertificates.Count131072.C038640
import PlattCertificates.Count131072.C038641
import PlattCertificates.Count131072.C038642
import PlattCertificates.Count131072.C038643
import PlattCertificates.Count131072.C038644
import PlattCertificates.Count131072.C038645
import PlattCertificates.Count131072.C038646
import PlattCertificates.Count131072.C038647
import PlattCertificates.Count131072.C038648
import PlattCertificates.Count131072.C038649
import PlattCertificates.Count131072.C038650
import PlattCertificates.Count131072.C038651
import PlattCertificates.Count131072.C038652
import PlattCertificates.Count131072.C038653
import PlattCertificates.Count131072.C038654
import PlattCertificates.Count131072.C038655
import PlattCertificates.Count131072.C038656
import PlattCertificates.Count131072.C038657
import PlattCertificates.Count131072.C038658
import PlattCertificates.Count131072.C038659
import PlattCertificates.Count131072.C038660
import PlattCertificates.Count131072.C038661
import PlattCertificates.Count131072.C038662
import PlattCertificates.Count131072.C038663
import PlattCertificates.Count131072.C038664
import PlattCertificates.Count131072.C038665
import PlattCertificates.Count131072.C038666
import PlattCertificates.Count131072.C038667
import PlattCertificates.Count131072.C038668
import PlattCertificates.Count131072.C038669
import PlattCertificates.Count131072.C038670
import PlattCertificates.Count131072.C038671
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000270
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts38640 : List PrefixCut := [⟨64,320257922,320258120⟩]
theorem checked38640 : checkPrefixCuts (2^48) 5068554241 10 Manual.Count131072.C038640.packed 64 cuts38640 = true := by
 decide +kernel
def cuts38641 : List PrefixCut := [⟨7,35929235,35929257⟩,
⟨64,330411885,330412082⟩]
theorem checked38641 : checkPrefixCuts (2^48) 5068685313 10 Manual.Count131072.C038641.packed 64 cuts38641 = true := by
 decide +kernel
def pointBounds38641 : List (Nat × Nat × Nat) := [(5068699648,108431522272431,108431907518506)]
theorem point_links_checked38641 : (cuts38641.take 1).map (fun c => (5068685313-1+2*2^10*c.k,108431486343196+c.lower,108431871589249+c.upper)) = pointBounds38641 := by
 decide +kernel
def cuts38642 : List PrefixCut := [⟨21,107118254,107118319⟩,
⟨64,326238608,326238808⟩]
theorem checked38642 : checkPrefixCuts (2^48) 5068816385 10 Manual.Count131072.C038642.packed 64 cuts38642 = true := by
 decide +kernel
def pointBounds38642 : List (Nat × Nat × Nat) := [(5068859392,108431923873335,108432309119650)]
theorem point_links_checked38642 : (cuts38642.take 1).map (fun c => (5068816385-1+2*2^10*c.k,108431816755081+c.lower,108432202001331+c.upper)) = pointBounds38642 := by
 decide +kernel
def cuts38643 : List PrefixCut := [⟨35,175915447,175915552⟩,
⟨64,319455715,319455904⟩]
theorem checked38643 : checkPrefixCuts (2^48) 5068947457 10 Manual.Count131072.C038643.packed 64 cuts38643 = true := by
 decide +kernel
def pointBounds38643 : List (Nat × Nat × Nat) := [(5069019136,108432318909136,108432704155691)]
theorem point_links_checked38643 : (cuts38643.take 1).map (fun c => (5068947457-1+2*2^10*c.k,108432142993689+c.lower,108432528240139+c.upper)) = pointBounds38643 := by
 decide +kernel
def cuts38644 : List PrefixCut := [⟨49,250205897,250206047⟩,
⟨64,325333321,325333516⟩]
theorem checked38644 : checkPrefixCuts (2^48) 5069078529 10 Manual.Count131072.C038644.packed 64 cuts38644 = true := by
 decide +kernel
def pointBounds38644 : List (Nat × Nat × Nat) := [(5069178880,108432712655301,108433097902090)]
theorem point_links_checked38644 : (cuts38644.take 1).map (fun c => (5069078529-1+2*2^10*c.k,108432462449404+c.lower,108432847696043+c.upper)) = pointBounds38644 := by
 decide +kernel
def cuts38645 : List PrefixCut := [⟨63,319605821,319606010⟩,
⟨64,325047267,325047460⟩]
theorem checked38645 : checkPrefixCuts (2^48) 5069209601 10 Manual.Count131072.C038645.packed 64 cuts38645 = true := by
 decide +kernel
def pointBounds38645 : List (Nat × Nat × Nat) := [(5069338624,108433107388546,108433492635569)]
theorem point_links_checked38645 : (cuts38645.take 1).map (fun c => (5069209601-1+2*2^10*c.k,108432787782725+c.lower,108433173029559+c.upper)) = pointBounds38645 := by
 decide +kernel
def cuts38646 : List PrefixCut := [⟨64,325316483,325316681⟩]
theorem checked38646 : checkPrefixCuts (2^48) 5069340673 10 Manual.Count131072.C038646.packed 64 cuts38646 = true := by
 decide +kernel
def cuts38647 : List PrefixCut := [⟨13,67183277,67183318⟩,
⟨64,323586891,323587089⟩]
theorem checked38647 : checkPrefixCuts (2^48) 5069471745 10 Manual.Count131072.C038647.packed 64 cuts38647 = true := by
 decide +kernel
def pointBounds38647 : List (Nat × Nat × Nat) := [(5069498368,108433505329752,108433890577018)]
theorem point_links_checked38647 : (cuts38647.take 1).map (fun c => (5069471745-1+2*2^10*c.k,108433438146475+c.lower,108433823393700+c.upper)) = pointBounds38647 := by
 decide +kernel
def cuts38648 : List PrefixCut := [⟨27,136194919,136195002⟩,
⟨64,321468682,321468877⟩]
theorem checked38648 : checkPrefixCuts (2^48) 5069602817 10 Manual.Count131072.C038648.packed 64 cuts38648 = true := by
 decide +kernel
def pointBounds38648 : List (Nat × Nat × Nat) := [(5069658112,108433897928285,108434283175791)]
theorem point_links_checked38648 : (cuts38648.take 1).map (fun c => (5069602817-1+2*2^10*c.k,108433761733366+c.lower,108434146980789+c.upper)) = pointBounds38648 := by
 decide +kernel
def cuts38649 : List PrefixCut := [⟨41,208700374,208700499⟩,
⟨64,323847743,323847938⟩]
theorem checked38649 : checkPrefixCuts (2^48) 5069733889 10 Manual.Count131072.C038649.packed 64 cuts38649 = true := by
 decide +kernel
def pointBounds38649 : List (Nat × Nat × Nat) := [(5069817856,108434291902422,108434677150165)]
theorem point_links_checked38649 : (cuts38649.take 1).map (fun c => (5069733889-1+2*2^10*c.k,108434083202048+c.lower,108434468449666+c.upper)) = pointBounds38649 := by
 decide +kernel
def cuts38650 : List PrefixCut := [⟨55,279924770,279924939⟩,
⟨64,325005283,325005482⟩]
theorem checked38650 : checkPrefixCuts (2^48) 5069864961 10 Manual.Count131072.C038650.packed 64 cuts38650 = true := by
 decide +kernel
def pointBounds38650 : List (Nat × Nat × Nat) := [(5069977600,108434686974561,108435072222543)]
theorem point_links_checked38650 : (cuts38650.take 1).map (fun c => (5069864961-1+2*2^10*c.k,108434407049791+c.lower,108434792297604+c.upper)) = pointBounds38650 := by
 decide +kernel
def cuts38651 : List PrefixCut := [⟨64,324164083,324164277⟩]
theorem checked38651 : checkPrefixCuts (2^48) 5069996033 10 Manual.Count131072.C038651.packed 64 cuts38651 = true := by
 decide +kernel
def cuts38652 : List PrefixCut := [⟨5,26703332,26703349⟩,
⟨64,325154998,325155192⟩]
theorem checked38652 : checkPrefixCuts (2^48) 5070127105 10 Manual.Count131072.C038652.packed 64 cuts38652 = true := by
 decide +kernel
def pointBounds38652 : List (Nat × Nat × Nat) := [(5070137344,108435082922489,108435468170712)]
theorem point_links_checked38652 : (cuts38652.take 1).map (fun c => (5070127105-1+2*2^10*c.k,108435056219157+c.lower,108435441467363+c.upper)) = pointBounds38652 := by
 decide +kernel
def cuts38653 : List PrefixCut := [⟨19,93764315,93764373⟩,
⟨64,324258349,324258543⟩]
theorem checked38653 : checkPrefixCuts (2^48) 5070258177 10 Manual.Count131072.C038653.packed 64 cuts38653 = true := by
 decide +kernel
def pointBounds38653 : List (Nat × Nat × Nat) := [(5070297088,108435475138470,108435860386928)]
theorem point_links_checked38653 : (cuts38653.take 1).map (fun c => (5070258177-1+2*2^10*c.k,108435381374155+c.lower,108435766622555+c.upper)) = pointBounds38653 := by
 decide +kernel
def cuts38654 : List PrefixCut := [⟨33,168371235,168371336⟩,
⟨64,327969338,327969533⟩]
theorem checked38654 : checkPrefixCuts (2^48) 5070389249 10 Manual.Count131072.C038654.packed 64 cuts38654 = true := by
 decide +kernel
def pointBounds38654 : List (Nat × Nat × Nat) := [(5070456832,108435874003739,108436259252434)]
theorem point_links_checked38654 : (cuts38654.take 1).map (fun c => (5070389249-1+2*2^10*c.k,108435705632504+c.lower,108436090881098+c.upper)) = pointBounds38654 := by
 decide +kernel
def cuts38655 : List PrefixCut := [⟨47,244306108,244306252⟩,
⟨64,328182910,328183105⟩]
theorem checked38655 : checkPrefixCuts (2^48) 5070520321 10 Manual.Count131072.C038655.packed 64 cuts38655 = true := by
 decide +kernel
def pointBounds38655 : List (Nat × Nat × Nat) := [(5070616576,108436277907950,108436663156883)]
theorem point_links_checked38655 : (cuts38655.take 1).map (fun c => (5070520321-1+2*2^10*c.k,108436033601842+c.lower,108436418850631+c.upper)) = pointBounds38655 := by
 decide +kernel
def cuts38656 : List PrefixCut := [⟨61,307857992,307858174⟩,
⟨64,322789966,322790157⟩]
theorem checked38656 : checkPrefixCuts (2^48) 5070651393 10 Manual.Count131072.C038656.packed 64 cuts38656 = true := by
 decide +kernel
def pointBounds38656 : List (Nat × Nat × Nat) := [(5070776320,108436669642744,108437054891910)]
theorem point_links_checked38656 : (cuts38656.take 1).map (fun c => (5070651393-1+2*2^10*c.k,108436361784752+c.lower,108436747033736+c.upper)) = pointBounds38656 := by
 decide +kernel
def cuts38657 : List PrefixCut := [⟨64,322948152,322948352⟩]
theorem checked38657 : checkPrefixCuts (2^48) 5070782465 10 Manual.Count131072.C038657.packed 64 cuts38657 = true := by
 decide +kernel
def cuts38658 : List PrefixCut := [⟨11,58782554,58782588⟩,
⟨64,329101105,329101296⟩]
theorem checked38658 : checkPrefixCuts (2^48) 5070913537 10 Manual.Count131072.C038658.packed 64 cuts38658 = true := by
 decide +kernel
def pointBounds38658 : List (Nat × Nat × Nat) := [(5070936064,108437066305424,108437451554833)]
theorem point_links_checked38658 : (cuts38658.take 1).map (fun c => (5070913537-1+2*2^10*c.k,108437007522870+c.lower,108437392772245+c.upper)) = pointBounds38658 := by
 decide +kernel
def cuts38659 : List PrefixCut := [⟨25,128995966,128996041⟩,
⟨64,326761347,326761537⟩]
theorem checked38659 : checkPrefixCuts (2^48) 5071044609 10 Manual.Count131072.C038659.packed 64 cuts38659 = true := by
 decide +kernel
def pointBounds38659 : List (Nat × Nat × Nat) := [(5071095808,108437465619941,108437850869582)]
theorem point_links_checked38659 : (cuts38659.take 1).map (fun c => (5071044609-1+2*2^10*c.k,108437336623975+c.lower,108437721873541+c.upper)) = pointBounds38659 := by
 decide +kernel
def cuts38660 : List PrefixCut := [⟨39,201037007,201037127⟩,
⟨64,326419874,326420068⟩]
theorem checked38660 : checkPrefixCuts (2^48) 5071175681 10 Manual.Count131072.C038660.packed 64 cuts38660 = true := by
 decide +kernel
def pointBounds38660 : List (Nat × Nat × Nat) := [(5071255552,108437864422329,108438249672205)]
theorem point_links_checked38660 : (cuts38660.take 1).map (fun c => (5071175681-1+2*2^10*c.k,108437663385322+c.lower,108438048635078+c.upper)) = pointBounds38660 := by
 decide +kernel
def cuts38661 : List PrefixCut := [⟨53,270243282,270243452⟩,
⟨64,324246837,324247039⟩]
theorem checked38661 : checkPrefixCuts (2^48) 5071306753 10 Manual.Count131072.C038661.packed 64 cuts38661 = true := by
 decide +kernel
def pointBounds38661 : List (Nat × Nat × Nat) := [(5071415296,108438260048478,108438645298598)]
theorem point_links_checked38661 : (cuts38661.take 1).map (fun c => (5071306753-1+2*2^10*c.k,108437989805196+c.lower,108438375055146+c.upper)) = pointBounds38661 := by
 decide +kernel
def cuts38662 : List PrefixCut := [⟨64,329122581,329122782⟩]
theorem checked38662 : checkPrefixCuts (2^48) 5071437825 10 Manual.Count131072.C038662.packed 64 cuts38662 = true := by
 decide +kernel
def cuts38663 : List PrefixCut := [⟨3,16261653,16261662⟩,
⟨64,325007039,325007238⟩]
theorem checked38663 : checkPrefixCuts (2^48) 5071568897 10 Manual.Count131072.C038663.packed 64 cuts38663 = true := by
 decide +kernel
def pointBounds38663 : List (Nat × Nat × Nat) := [(5071575040,108438659436267,108439044686629)]
theorem point_links_checked38663 : (cuts38663.take 1).map (fun c => (5071568897-1+2*2^10*c.k,108438643174614+c.lower,108439028424967+c.upper)) = pointBounds38663 := by
 decide +kernel
def cuts38664 : List PrefixCut := [⟨17,82859902,82859952⟩,
⟨64,323167170,323167366⟩]
theorem checked38664 : checkPrefixCuts (2^48) 5071699969 10 Manual.Count131072.C038664.packed 64 cuts38664 = true := by
 decide +kernel
def pointBounds38664 : List (Nat × Nat × Nat) := [(5071734784,108439051041555,108439436292157)]
theorem point_links_checked38664 : (cuts38664.take 1).map (fun c => (5071699969-1+2*2^10*c.k,108438968181653+c.lower,108439353432205+c.upper)) = pointBounds38664 := by
 decide +kernel
def cuts38665 : List PrefixCut := [⟨31,154338096,154338192⟩,
⟨64,323380813,323381010⟩]
theorem checked38665 : checkPrefixCuts (2^48) 5071831041 10 Manual.Count131072.C038665.packed 64 cuts38665 = true := by
 decide +kernel
def pointBounds38665 : List (Nat × Nat × Nat) := [(5071894528,108439445686919,108439830937763)]
theorem point_links_checked38665 : (cuts38665.take 1).map (fun c => (5071831041-1+2*2^10*c.k,108439291348823+c.lower,108439676599571+c.upper)) = pointBounds38665 := by
 decide +kernel
def cuts38666 : List PrefixCut := [⟨45,228420512,228420647⟩,
⟨64,328589047,328589244⟩]
theorem checked38666 : checkPrefixCuts (2^48) 5071962113 10 Manual.Count131072.C038666.packed 64 cuts38666 = true := by
 decide +kernel
def pointBounds38666 : List (Nat × Nat × Nat) := [(5072054272,108439843150148,108440228401228)]
theorem point_links_checked38666 : (cuts38666.take 1).map (fun c => (5071962113-1+2*2^10*c.k,108439614729636+c.lower,108439999980581+c.upper)) = pointBounds38666 := by
 decide +kernel
def cuts38667 : List PrefixCut := [⟨59,299890431,299890614⟩,
⟨64,325639387,325639586⟩]
theorem checked38667 : checkPrefixCuts (2^48) 5072093185 10 Manual.Count131072.C038667.packed 64 cuts38667 = true := by
 decide +kernel
def pointBounds38667 : List (Nat × Nat × Nat) := [(5072214016,108440243209114,108440628460439)]
theorem point_links_checked38667 : (cuts38667.take 1).map (fun c => (5072093185-1+2*2^10*c.k,108439943318683+c.lower,108440328569825+c.upper)) = pointBounds38667 := by
 decide +kernel
def cuts38668 : List PrefixCut := [⟨64,323966203,323966398⟩]
theorem checked38668 : checkPrefixCuts (2^48) 5072224257 10 Manual.Count131072.C038668.packed 64 cuts38668 = true := by
 decide +kernel
def cuts38669 : List PrefixCut := [⟨9,45114875,45114902⟩,
⟨64,323347405,323347597⟩]
theorem checked38669 : checkPrefixCuts (2^48) 5072355329 10 Manual.Count131072.C038669.packed 64 cuts38669 = true := by
 decide +kernel
def pointBounds38669 : List (Nat × Nat × Nat) := [(5072373760,108440638039148,108441023290711)]
theorem point_links_checked38669 : (cuts38669.take 1).map (fun c => (5072355329-1+2*2^10*c.k,108440592924273+c.lower,108440978175809+c.upper)) = pointBounds38669 := by
 decide +kernel
def cuts38670 : List PrefixCut := [⟨23,118527194,118527266⟩,
⟨64,323505543,323505737⟩]
theorem checked38670 : checkPrefixCuts (2^48) 5072486401 10 Manual.Count131072.C038670.packed 64 cuts38670 = true := by
 decide +kernel
def pointBounds38670 : List (Nat × Nat × Nat) := [(5072533504,108441034798872,108441420050672)]
theorem point_links_checked38670 : (cuts38670.take 1).map (fun c => (5072486401-1+2*2^10*c.k,108440916271678+c.lower,108441301523406+c.upper)) = pointBounds38670 := by
 decide +kernel
def cuts38671 : List PrefixCut := [⟨37,188883426,188883537⟩,
⟨64,326549032,326549224⟩]
theorem checked38671 : checkPrefixCuts (2^48) 5072617473 10 Manual.Count131072.C038671.packed 64 cuts38671 = true := by
 decide +kernel
def pointBounds38671 : List (Nat × Nat × Nat) := [(5072693248,108441428660647,108441813912680)]
theorem point_links_checked38671 : (cuts38671.take 1).map (fun c => (5072617473-1+2*2^10*c.k,108441239777221+c.lower,108441625029143+c.upper)) = pointBounds38671 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000270
