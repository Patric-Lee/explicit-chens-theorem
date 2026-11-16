import PlattAssemblyKernel
import PlattCertificates.Count131072.C061568
import PlattCertificates.Count131072.C061569
import PlattCertificates.Count131072.C061570
import PlattCertificates.Count131072.C061571
import PlattCertificates.Count131072.C061572
import PlattCertificates.Count131072.C061573
import PlattCertificates.Count131072.C061574
import PlattCertificates.Count131072.C061575
import PlattCertificates.Count131072.C061576
import PlattCertificates.Count131072.C061577
import PlattCertificates.Count131072.C061578
import PlattCertificates.Count131072.C061579
import PlattCertificates.Count131072.C061580
import PlattCertificates.Count131072.C061581
import PlattCertificates.Count131072.C061582
import PlattCertificates.Count131072.C061583
import PlattCertificates.Count131072.C061584
import PlattCertificates.Count131072.C061585
import PlattCertificates.Count131072.C061586
import PlattCertificates.Count131072.C061587
import PlattCertificates.Count131072.C061588
import PlattCertificates.Count131072.C061589
import PlattCertificates.Count131072.C061590
import PlattCertificates.Count131072.C061591
import PlattCertificates.Count131072.C061592
import PlattCertificates.Count131072.C061593
import PlattCertificates.Count131072.C061594
import PlattCertificates.Count131072.C061595
import PlattCertificates.Count131072.C061596
import PlattCertificates.Count131072.C061597
import PlattCertificates.Count131072.C061598
import PlattCertificates.Count131072.C061599
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000049
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts61568 : List PrefixCut := [⟨64,198158953,198159062⟩]
theorem checked61568 : checkPrefixCuts (2^48) 8073773057 10 Manual.Count131072.C061568.packed 64 cuts61568 = true := by
 decide +kernel
def cuts61569 : List PrefixCut := [⟨36,110652448,110652509⟩,
⟨64,198295169,198295277⟩]
theorem checked61569 : checkPrefixCuts (2^48) 8073904129 10 Manual.Count131072.C061569.packed 64 cuts61569 = true := by
 decide +kernel
def pointBounds61569 : List (Nat × Nat × Nat) := [(8073977856,114235479498163,114235868087712)]
theorem point_links_checked61569 : (cuts61569.take 1).map (fun c => (8073904129-1+2*2^10*c.k,114235368845715+c.lower,114235757435203+c.upper)) = pointBounds61569 := by
 decide +kernel
def cuts61570 : List PrefixCut := [⟨64,202754201,202754313⟩]
theorem checked61570 : checkPrefixCuts (2^48) 8074035201 10 Manual.Count131072.C061570.packed 64 cuts61570 = true := by
 decide +kernel
def cuts61571 : List PrefixCut := [⟨32,100225461,100225519⟩,
⟨64,201391353,201391471⟩]
theorem checked61571 : checkPrefixCuts (2^48) 8074166273 10 Manual.Count131072.C061571.packed 64 cuts61571 = true := by
 decide +kernel
def pointBounds61571 : List (Nat × Nat × Nat) := [(8074231808,114235870120546,114236258710312)]
theorem point_links_checked61571 : (cuts61571.take 1).map (fun c => (8074166273-1+2*2^10*c.k,114235769895085+c.lower,114236158484793+c.upper)) = pointBounds61571 := by
 decide +kernel
def cuts61572 : List PrefixCut := [⟨64,201109194,201109309⟩]
theorem checked61572 : checkPrefixCuts (2^48) 8074297345 10 Manual.Count131072.C061572.packed 64 cuts61572 = true := by
 decide +kernel
def cuts61573 : List PrefixCut := [⟨28,88300169,88300218⟩,
⟨64,199711554,199711667⟩]
theorem checked61573 : checkPrefixCuts (2^48) 8074428417 10 Manual.Count131072.C061573.packed 64 cuts61573 = true := by
 decide +kernel
def pointBounds61573 : List (Nat × Nat × Nat) := [(8074485760,114236260695801,114236649285791)]
theorem point_links_checked61573 : (cuts61573.take 1).map (fun c => (8074428417-1+2*2^10*c.k,114236172395632+c.lower,114236560985573+c.upper)) = pointBounds61573 := by
 decide +kernel
def cuts61574 : List PrefixCut := [⟨64,203054786,203054898⟩]
theorem checked61574 : checkPrefixCuts (2^48) 8074559489 10 Manual.Count131072.C061574.packed 64 cuts61574 = true := by
 decide +kernel
def cuts61575 : List PrefixCut := [⟨24,73830940,73830985⟩,
⟨64,199182176,199182292⟩]
theorem checked61575 : checkPrefixCuts (2^48) 8074690561 10 Manual.Count131072.C061575.packed 64 cuts61575 = true := by
 decide +kernel
def pointBounds61575 : List (Nat × Nat × Nat) := [(8074739712,114236648992912,114237037583123)]
theorem point_links_checked61575 : (cuts61575.take 1).map (fun c => (8074690561-1+2*2^10*c.k,114236575161972+c.lower,114236963752138+c.upper)) = pointBounds61575 := by
 decide +kernel
def cuts61576 : List PrefixCut := [⟨64,199248680,199248797⟩]
theorem checked61576 : checkPrefixCuts (2^48) 8074821633 10 Manual.Count131072.C061576.packed 64 cuts61576 = true := by
 decide +kernel
def cuts61577 : List PrefixCut := [⟨20,62430118,62430155⟩,
⟨64,201336879,201336996⟩]
theorem checked61577 : checkPrefixCuts (2^48) 8074952705 10 Manual.Count131072.C061577.packed 64 cuts61577 = true := by
 decide +kernel
def pointBounds61577 : List (Nat × Nat × Nat) := [(8074993664,114237036022946,114237424613382)]
theorem point_links_checked61577 : (cuts61577.take 1).map (fun c => (8074952705-1+2*2^10*c.k,114236973592828+c.lower,114237362183227+c.upper)) = pointBounds61577 := by
 decide +kernel
def cuts61578 : List PrefixCut := [⟨64,200218187,200218307⟩]
theorem checked61578 : checkPrefixCuts (2^48) 8075083777 10 Manual.Count131072.C061578.packed 64 cuts61578 = true := by
 decide +kernel
def cuts61579 : List PrefixCut := [⟨16,50751173,50751203⟩,
⟨64,201260645,201260762⟩]
theorem checked61579 : checkPrefixCuts (2^48) 8075214849 10 Manual.Count131072.C061579.packed 64 cuts61579 = true := by
 decide +kernel
def pointBounds61579 : List (Nat × Nat × Nat) := [(8075247616,114237425899067,114237814489733)]
theorem point_links_checked61579 : (cuts61579.take 1).map (fun c => (8075214849-1+2*2^10*c.k,114237375147894+c.lower,114237763738530+c.upper)) = pointBounds61579 := by
 decide +kernel
def cuts61580 : List PrefixCut := [⟨64,201989327,201989441⟩]
theorem checked61580 : checkPrefixCuts (2^48) 8075345921 10 Manual.Count131072.C061580.packed 64 cuts61580 = true := by
 decide +kernel
def cuts61581 : List PrefixCut := [⟨12,36772511,36772531⟩,
⟨64,199511344,199511457⟩]
theorem checked61581 : checkPrefixCuts (2^48) 8075476993 10 Manual.Count131072.C061581.packed 64 cuts61581 = true := by
 decide +kernel
def pointBounds61581 : List (Nat × Nat × Nat) := [(8075501568,114237815170377,114238203761264)]
theorem point_links_checked61581 : (cuts61581.take 1).map (fun c => (8075476993-1+2*2^10*c.k,114237778397866+c.lower,114238166988733+c.upper)) = pointBounds61581 := by
 decide +kernel
def cuts61582 : List PrefixCut := [⟨64,202331328,202331440⟩]
theorem checked61582 : checkPrefixCuts (2^48) 8075608065 10 Manual.Count131072.C061582.packed 64 cuts61582 = true := by
 decide +kernel
def cuts61583 : List PrefixCut := [⟨8,24014645,24014657⟩,
⟨64,198319809,198319924⟩]
theorem checked61583 : checkPrefixCuts (2^48) 8075739137 10 Manual.Count131072.C061583.packed 64 cuts61583 = true := by
 decide +kernel
def pointBounds61583 : List (Nat × Nat × Nat) := [(8075755520,114238204255183,114238592846287)]
theorem point_links_checked61583 : (cuts61583.take 1).map (fun c => (8075739137-1+2*2^10*c.k,114238180240538+c.lower,114238568831630+c.upper)) = pointBounds61583 := by
 decide +kernel
def cuts61584 : List PrefixCut := [⟨64,199013666,199013783⟩]
theorem checked61584 : checkPrefixCuts (2^48) 8075870209 10 Manual.Count131072.C061584.packed 64 cuts61584 = true := by
 decide +kernel
def cuts61585 : List PrefixCut := [⟨4,12128925,12128932⟩,
⟨64,198243671,198243784⟩]
theorem checked61585 : checkPrefixCuts (2^48) 8076001281 10 Manual.Count131072.C061585.packed 64 cuts61585 = true := by
 decide +kernel
def pointBounds61585 : List (Nat × Nat × Nat) := [(8076009472,114238589702938,114238978294269)]
theorem point_links_checked61585 : (cuts61585.take 1).map (fun c => (8076001281-1+2*2^10*c.k,114238577574013+c.lower,114238966165337+c.upper)) = pointBounds61585 := by
 decide +kernel
def cuts61586 : List PrefixCut := [⟨64,203538025,203538144⟩]
theorem checked61586 : checkPrefixCuts (2^48) 8076132353 10 Manual.Count131072.C061586.packed 64 cuts61586 = true := by
 decide +kernel
def pointBounds61586 : List (Nat × Nat × Nat) := [(8076263424,114238979355709,114239367947265)]
theorem point_links_checked61586 : (cuts61586.take 1).map (fun c => (8076132353-1+2*2^10*c.k,114238775817684+c.lower,114239164409121+c.upper)) = pointBounds61586 := by
 decide +kernel
def cuts61587 : List PrefixCut := [⟨64,199526760,199526877⟩]
theorem checked61587 : checkPrefixCuts (2^48) 8076263425 10 Manual.Count131072.C061587.packed 64 cuts61587 = true := by
 decide +kernel
def cuts61588 : List PrefixCut := [⟨60,192204865,192204974⟩,
⟨64,204751227,204751343⟩]
theorem checked61588 : checkPrefixCuts (2^48) 8076394497 10 Manual.Count131072.C061588.packed 64 cuts61588 = true := by
 decide +kernel
def pointBounds61588 : List (Nat × Nat × Nat) := [(8076517376,114239371087334,114239759679116)]
theorem point_links_checked61588 : (cuts61588.take 1).map (fun c => (8076394497-1+2*2^10*c.k,114239178882469+c.lower,114239567474142+c.upper)) = pointBounds61588 := by
 decide +kernel
def cuts61589 : List PrefixCut := [⟨64,199206643,199206755⟩]
theorem checked61589 : checkPrefixCuts (2^48) 8076525569 10 Manual.Count131072.C061589.packed 64 cuts61589 = true := by
 decide +kernel
def cuts61590 : List PrefixCut := [⟨56,176202478,176202570⟩,
⟨64,200318604,200318709⟩]
theorem checked61590 : checkPrefixCuts (2^48) 8076656641 10 Manual.Count131072.C061590.packed 64 cuts61590 = true := by
 decide +kernel
def pointBounds61590 : List (Nat × Nat × Nat) := [(8076771328,114239759042817,114240147634810)]
theorem point_links_checked61590 : (cuts61590.take 1).map (fun c => (8076656641-1+2*2^10*c.k,114239582840339+c.lower,114239971432240+c.upper)) = pointBounds61590 := by
 decide +kernel
def cuts61591 : List PrefixCut := [⟨64,202580570,202580683⟩]
theorem checked61591 : checkPrefixCuts (2^48) 8076787713 10 Manual.Count131072.C061591.packed 64 cuts61591 = true := by
 decide +kernel
def cuts61592 : List PrefixCut := [⟨52,162187533,162187628⟩,
⟨64,200486340,200486457⟩]
theorem checked61592 : checkPrefixCuts (2^48) 8076918785 10 Manual.Count131072.C061592.packed 64 cuts61592 = true := by
 decide +kernel
def pointBounds61592 : List (Nat × Nat × Nat) := [(8077025280,114240147927046,114240536519260)]
theorem point_links_checked61592 : (cuts61592.take 1).map (fun c => (8076918785-1+2*2^10*c.k,114239985739513+c.lower,114240374331632+c.upper)) = pointBounds61592 := by
 decide +kernel
def cuts61593 : List PrefixCut := [⟨64,199960366,199960480⟩]
theorem checked61593 : checkPrefixCuts (2^48) 8077049857 10 Manual.Count131072.C061593.packed 64 cuts61593 = true := by
 decide +kernel
def cuts61594 : List PrefixCut := [⟨48,148835591,148835668⟩,
⟨64,199225314,199225422⟩]
theorem checked61594 : checkPrefixCuts (2^48) 8077180929 10 Manual.Count131072.C061594.packed 64 cuts61594 = true := by
 decide +kernel
def pointBounds61594 : List (Nat × Nat × Nat) := [(8077279232,114240535021810,114240923614237)]
theorem point_links_checked61594 : (cuts61594.take 1).map (fun c => (8077180929-1+2*2^10*c.k,114240386186219+c.lower,114240774778569+c.upper)) = pointBounds61594 := by
 decide +kernel
def cuts61595 : List PrefixCut := [⟨64,202811358,202811469⟩]
theorem checked61595 : checkPrefixCuts (2^48) 8077312001 10 Manual.Count131072.C061595.packed 64 cuts61595 = true := by
 decide +kernel
def cuts61596 : List PrefixCut := [⟨44,135066321,135066401⟩,
⟨64,197267419,197267534⟩]
theorem checked61596 : checkPrefixCuts (2^48) 8077443073 10 Manual.Count131072.C061596.packed 64 cuts61596 = true := by
 decide +kernel
def pointBounds61596 : List (Nat × Nat × Nat) := [(8077533184,114240923289212,114241311881861)]
theorem point_links_checked61596 : (cuts61596.take 1).map (fun c => (8077443073-1+2*2^10*c.k,114240788222891+c.lower,114241176815460+c.upper)) = pointBounds61596 := by
 decide +kernel
def cuts61597 : List PrefixCut := [⟨64,198902000,198902120⟩]
theorem checked61597 : checkPrefixCuts (2^48) 8077574145 10 Manual.Count131072.C061597.packed 64 cuts61597 = true := by
 decide +kernel
def cuts61598 : List PrefixCut := [⟨40,127500495,127500566⟩,
⟨64,204439222,204439336⟩]
theorem checked61598 : checkPrefixCuts (2^48) 8077705217 10 Manual.Count131072.C061598.packed 64 cuts61598 = true := by
 decide +kernel
def pointBounds61598 : List (Nat × Nat × Nat) := [(8077787136,114241311892805,114241700485680)]
theorem point_links_checked61598 : (cuts61598.take 1).map (fun c => (8077705217-1+2*2^10*c.k,114241184392310+c.lower,114241572985114+c.upper)) = pointBounds61598 := by
 decide +kernel
def cuts61599 : List PrefixCut := [⟨64,199313684,199313800⟩]
theorem checked61599 : checkPrefixCuts (2^48) 8077836289 10 Manual.Count131072.C061599.packed 64 cuts61599 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000049
