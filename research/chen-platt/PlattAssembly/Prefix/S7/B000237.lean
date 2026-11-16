import PlattAssemblyKernel
import PlattCertificates.Count131072.C067584
import PlattCertificates.Count131072.C067585
import PlattCertificates.Count131072.C067586
import PlattCertificates.Count131072.C067587
import PlattCertificates.Count131072.C067588
import PlattCertificates.Count131072.C067589
import PlattCertificates.Count131072.C067590
import PlattCertificates.Count131072.C067591
import PlattCertificates.Count131072.C067592
import PlattCertificates.Count131072.C067593
import PlattCertificates.Count131072.C067594
import PlattCertificates.Count131072.C067595
import PlattCertificates.Count131072.C067596
import PlattCertificates.Count131072.C067597
import PlattCertificates.Count131072.C067598
import PlattCertificates.Count131072.C067599
import PlattCertificates.Count131072.C067600
import PlattCertificates.Count131072.C067601
import PlattCertificates.Count131072.C067602
import PlattCertificates.Count131072.C067603
import PlattCertificates.Count131072.C067604
import PlattCertificates.Count131072.C067605
import PlattCertificates.Count131072.C067606
import PlattCertificates.Count131072.C067607
import PlattCertificates.Count131072.C067608
import PlattCertificates.Count131072.C067609
import PlattCertificates.Count131072.C067610
import PlattCertificates.Count131072.C067611
import PlattCertificates.Count131072.C067612
import PlattCertificates.Count131072.C067613
import PlattCertificates.Count131072.C067614
import PlattCertificates.Count131072.C067615
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000237
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts67584 : List PrefixCut := [⟨45,129393319,129393397⟩,
⟨64,182084025,182084133⟩]
theorem checked67584 : checkPrefixCuts (2^48) 8862302209 10 Manual.Count131072.C067584.packed 64 cuts67584 = true := by
 decide +kernel
def pointBounds67584 : List (Nat × Nat × Nat) := [(8862394368,115382782629644,115383171882180)]
theorem point_links_checked67584 : (cuts67584.take 1).map (fun c => (8862302209-1+2*2^10*c.k,115382653236325+c.lower,115383042488783+c.upper)) = pointBounds67584 := by
 decide +kernel
def cuts67585 : List PrefixCut := [⟨64,182335400,182335502⟩]
theorem checked67585 : checkPrefixCuts (2^48) 8862433281 10 Manual.Count131072.C067585.packed 64 cuts67585 = true := by
 decide +kernel
def cuts67586 : List PrefixCut := [⟨53,149461561,149461653⟩,
⟨64,181633988,181634098⟩]
theorem checked67586 : checkPrefixCuts (2^48) 8862564353 10 Manual.Count131072.C067586.packed 64 cuts67586 = true := by
 decide +kernel
def pointBounds67586 : List (Nat × Nat × Nat) := [(8862672896,115383167117311,115383556370071)]
theorem point_links_checked67586 : (cuts67586.take 1).map (fun c => (8862564353-1+2*2^10*c.k,115383017655750+c.lower,115383406908418+c.upper)) = pointBounds67586 := by
 decide +kernel
def cuts67587 : List PrefixCut := [⟨64,183663920,183664027⟩]
theorem checked67587 : checkPrefixCuts (2^48) 8862695425 10 Manual.Count131072.C067587.packed 64 cuts67587 = true := by
 decide +kernel
def cuts67588 : List PrefixCut := [⟨61,173307879,173307984⟩,
⟨64,181819181,181819289⟩]
theorem checked67588 : checkPrefixCuts (2^48) 8862826497 10 Manual.Count131072.C067588.packed 64 cuts67588 = true := by
 decide +kernel
def pointBounds67588 : List (Nat × Nat × Nat) := [(8862951424,115383556261537,115383945514527)]
theorem point_links_checked67588 : (cuts67588.take 1).map (fun c => (8862826497-1+2*2^10*c.k,115383382953658+c.lower,115383772206543+c.upper)) = pointBounds67588 := by
 decide +kernel
def cuts67589 : List PrefixCut := [⟨64,183340899,183341000⟩]
theorem checked67589 : checkPrefixCuts (2^48) 8862957569 10 Manual.Count131072.C067589.packed 64 cuts67589 = true := by
 decide +kernel
def cuts67590 : List PrefixCut := [⟨64,178638021,178638125⟩]
theorem checked67590 : checkPrefixCuts (2^48) 8863088641 10 Manual.Count131072.C067590.packed 64 cuts67590 = true := by
 decide +kernel
def cuts67591 : List PrefixCut := [⟨5,13909835,13909845⟩,
⟨64,181938138,181938245⟩]
theorem checked67591 : checkPrefixCuts (2^48) 8863219713 10 Manual.Count131072.C067591.packed 64 cuts67591 = true := by
 decide +kernel
def pointBounds67591 : List (Nat × Nat × Nat) := [(8863229952,115383940661594,115384329914802)]
theorem point_links_checked67591 : (cuts67591.take 1).map (fun c => (8863219713-1+2*2^10*c.k,115383926751759+c.lower,115384316004957+c.upper)) = pointBounds67591 := by
 decide +kernel
def cuts67592 : List PrefixCut := [⟨64,181046262,181046365⟩]
theorem checked67592 : checkPrefixCuts (2^48) 8863350785 10 Manual.Count131072.C067592.packed 64 cuts67592 = true := by
 decide +kernel
def cuts67593 : List PrefixCut := [⟨13,36996496,36996517⟩,
⟨64,178090237,178090343⟩]
theorem checked67593 : checkPrefixCuts (2^48) 8863481857 10 Manual.Count131072.C067593.packed 64 cuts67593 = true := by
 decide +kernel
def pointBounds67593 : List (Nat × Nat × Nat) := [(8863508480,115384326732655,115384715986084)]
theorem point_links_checked67593 : (cuts67593.take 1).map (fun c => (8863481857-1+2*2^10*c.k,115384289736159+c.lower,115384678989567+c.upper)) = pointBounds67593 := by
 decide +kernel
def cuts67594 : List PrefixCut := [⟨64,181231433,181231546⟩]
theorem checked67594 : checkPrefixCuts (2^48) 8863612929 10 Manual.Count131072.C067594.packed 64 cuts67594 = true := by
 decide +kernel
def cuts67595 : List PrefixCut := [⟨21,59383123,59383158⟩,
⟨64,182848293,182848397⟩]
theorem checked67595 : checkPrefixCuts (2^48) 8863744001 10 Manual.Count131072.C067595.packed 64 cuts67595 = true := by
 decide +kernel
def pointBounds67595 : List (Nat × Nat × Nat) := [(8863787008,115384708440952,115385097694614)]
theorem point_links_checked67595 : (cuts67595.take 1).map (fun c => (8863744001-1+2*2^10*c.k,115384649057829+c.lower,115385038311456+c.upper)) = pointBounds67595 := by
 decide +kernel
def cuts67596 : List PrefixCut := [⟨64,180972041,180972148⟩]
theorem checked67596 : checkPrefixCuts (2^48) 8863875073 10 Manual.Count131072.C067596.packed 64 cuts67596 = true := by
 decide +kernel
def cuts67597 : List PrefixCut := [⟨29,83895941,83895994⟩,
⟨64,181667971,181668082⟩]
theorem checked67597 : checkPrefixCuts (2^48) 8864006145 10 Manual.Count131072.C067597.packed 64 cuts67597 = true := by
 decide +kernel
def pointBounds67597 : List (Nat × Nat × Nat) := [(8864065536,115385096774104,115385486027995)]
theorem point_links_checked67597 : (cuts67597.take 1).map (fun c => (8864006145-1+2*2^10*c.k,115385012878163+c.lower,115385402132001+c.upper)) = pointBounds67597 := by
 decide +kernel
def cuts67598 : List PrefixCut := [⟨64,182998944,182999048⟩]
theorem checked67598 : checkPrefixCuts (2^48) 8864137217 10 Manual.Count131072.C067598.packed 64 cuts67598 = true := by
 decide +kernel
def cuts67599 : List PrefixCut := [⟨37,104628580,104628642⟩,
⟨64,182900978,182901086⟩]
theorem checked67599 : checkPrefixCuts (2^48) 8864268289 10 Manual.Count131072.C067599.packed 64 cuts67599 = true := by
 decide +kernel
def pointBounds67599 : List (Nat × Nat × Nat) := [(8864344064,115385482173658,115385871427773)]
theorem point_links_checked67599 : (cuts67599.take 1).map (fun c => (8864268289-1+2*2^10*c.k,115385377545078+c.lower,115385766799131+c.upper)) = pointBounds67599 := by
 decide +kernel
def cuts67600 : List PrefixCut := [⟨64,180358045,180358146⟩]
theorem checked67600 : checkPrefixCuts (2^48) 8864399361 10 Manual.Count131072.C067600.packed 64 cuts67600 = true := by
 decide +kernel
def cuts67601 : List PrefixCut := [⟨45,127138113,127138193⟩,
⟨64,182514540,182514653⟩]
theorem checked67601 : checkPrefixCuts (2^48) 8864530433 10 Manual.Count131072.C067601.packed 64 cuts67601 = true := by
 decide +kernel
def pointBounds67601 : List (Nat × Nat × Nat) := [(8864622592,115385867942214,115386257196556)]
theorem point_links_checked67601 : (cuts67601.take 1).map (fun c => (8864530433-1+2*2^10*c.k,115385740804101+c.lower,115386130058363+c.upper)) = pointBounds67601 := by
 decide +kernel
def cuts67602 : List PrefixCut := [⟨64,183972454,183972559⟩]
theorem checked67602 : checkPrefixCuts (2^48) 8864661505 10 Manual.Count131072.C067602.packed 64 cuts67602 = true := by
 decide +kernel
def cuts67603 : List PrefixCut := [⟨53,151075091,151075182⟩,
⟨64,182540897,182541008⟩]
theorem checked67603 : checkPrefixCuts (2^48) 8864792577 10 Manual.Count131072.C067603.packed 64 cuts67603 = true := by
 decide +kernel
def pointBounds67603 : List (Nat × Nat × Nat) := [(8864901120,115386258366186,115386647620757)]
theorem point_links_checked67603 : (cuts67603.take 1).map (fun c => (8864792577-1+2*2^10*c.k,115386107291095+c.lower,115386496545575+c.upper)) = pointBounds67603 := by
 decide +kernel
def cuts67604 : List PrefixCut := [⟨64,183204961,183205066⟩]
theorem checked67604 : checkPrefixCuts (2^48) 8864923649 10 Manual.Count131072.C067604.packed 64 cuts67604 = true := by
 decide +kernel
def cuts67605 : List PrefixCut := [⟨61,170819498,170819605⟩,
⟨64,179201657,179201769⟩]
theorem checked67605 : checkPrefixCuts (2^48) 8865054721 10 Manual.Count131072.C067605.packed 64 cuts67605 = true := by
 decide +kernel
def pointBounds67605 : List (Nat × Nat × Nat) := [(8865179648,115386643856451,115387033111254)]
theorem point_links_checked67605 : (cuts67605.take 1).map (fun c => (8865054721-1+2*2^10*c.k,115386473036953+c.lower,115386862291649+c.upper)) = pointBounds67605 := by
 decide +kernel
def cuts67606 : List PrefixCut := [⟨64,183326561,183326669⟩]
theorem checked67606 : checkPrefixCuts (2^48) 8865185793 10 Manual.Count131072.C067606.packed 64 cuts67606 = true := by
 decide +kernel
def cuts67607 : List PrefixCut := [⟨64,182530094,182530200⟩]
theorem checked67607 : checkPrefixCuts (2^48) 8865316865 10 Manual.Count131072.C067607.packed 64 cuts67607 = true := by
 decide +kernel
def cuts67608 : List PrefixCut := [⟨5,13525345,13525352⟩,
⟨64,181638421,181638526⟩]
theorem checked67608 : checkPrefixCuts (2^48) 8865447937 10 Manual.Count131072.C067608.packed 64 cuts67608 = true := by
 decide +kernel
def pointBounds67608 : List (Nat × Nat × Nat) := [(8865458176,115387031620610,115387420875639)]
theorem point_links_checked67608 : (cuts67608.take 1).map (fun c => (8865447937-1+2*2^10*c.k,115387018095265+c.lower,115387407350287+c.upper)) = pointBounds67608 := by
 decide +kernel
def cuts67609 : List PrefixCut := [⟨64,178937067,178937180⟩]
theorem checked67609 : checkPrefixCuts (2^48) 8865579009 10 Manual.Count131072.C067609.packed 64 cuts67609 = true := by
 decide +kernel
def cuts67610 : List PrefixCut := [⟨13,35780747,35780769⟩,
⟨64,180140865,180140971⟩]
theorem checked67610 : checkPrefixCuts (2^48) 8865710081 10 Manual.Count131072.C067610.packed 64 cuts67610 = true := by
 decide +kernel
def pointBounds67610 : List (Nat × Nat × Nat) := [(8865736704,115387414451500,115387803706762)]
theorem point_links_checked67610 : (cuts67610.take 1).map (fun c => (8865710081-1+2*2^10*c.k,115387378670753+c.lower,115387767925993+c.upper)) = pointBounds67610 := by
 decide +kernel
def cuts67611 : List PrefixCut := [⟨64,181566868,181566974⟩]
theorem checked67611 : checkPrefixCuts (2^48) 8865841153 10 Manual.Count131072.C067611.packed 64 cuts67611 = true := by
 decide +kernel
def cuts67612 : List PrefixCut := [⟨21,60574612,60574648⟩,
⟨64,181468959,181469065⟩]
theorem checked67612 : checkPrefixCuts (2^48) 8865972225 10 Manual.Count131072.C067612.packed 64 cuts67612 = true := by
 decide +kernel
def pointBounds67612 : List (Nat × Nat × Nat) := [(8866015232,115387800953098,115388190208586)]
theorem point_links_checked67612 : (cuts67612.take 1).map (fun c => (8865972225-1+2*2^10*c.k,115387740378486+c.lower,115388129633938+c.upper)) = pointBounds67612 := by
 decide +kernel
def cuts67613 : List PrefixCut := [⟨64,179942413,179942514⟩]
theorem checked67613 : checkPrefixCuts (2^48) 8866103297 10 Manual.Count131072.C067613.packed 64 cuts67613 = true := by
 decide +kernel
def cuts67614 : List PrefixCut := [⟨29,81049398,81049449⟩,
⟨64,181654045,181654154⟩]
theorem checked67614 : checkPrefixCuts (2^48) 8866234369 10 Manual.Count131072.C067614.packed 64 cuts67614 = true := by
 decide +kernel
def pointBounds67614 : List (Nat × Nat × Nat) := [(8866293760,115388182839256,115388572094966)]
theorem point_links_checked67614 : (cuts67614.take 1).map (fun c => (8866234369-1+2*2^10*c.k,115388101789858+c.lower,115388491045517+c.upper)) = pointBounds67614 := by
 decide +kernel
def cuts67615 : List PrefixCut := [⟨64,180159305,180159416⟩]
theorem checked67615 : checkPrefixCuts (2^48) 8866365441 10 Manual.Count131072.C067615.packed 64 cuts67615 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000237
