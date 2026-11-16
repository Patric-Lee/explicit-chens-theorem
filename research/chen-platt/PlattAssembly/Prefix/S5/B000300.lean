import PlattAssemblyKernel
import PlattCertificates.Count131072.C049600
import PlattCertificates.Count131072.C049601
import PlattCertificates.Count131072.C049602
import PlattCertificates.Count131072.C049603
import PlattCertificates.Count131072.C049604
import PlattCertificates.Count131072.C049605
import PlattCertificates.Count131072.C049606
import PlattCertificates.Count131072.C049607
import PlattCertificates.Count131072.C049608
import PlattCertificates.Count131072.C049609
import PlattCertificates.Count131072.C049610
import PlattCertificates.Count131072.C049611
import PlattCertificates.Count131072.C049612
import PlattCertificates.Count131072.C049613
import PlattCertificates.Count131072.C049614
import PlattCertificates.Count131072.C049615
import PlattCertificates.Count131072.C049616
import PlattCertificates.Count131072.C049617
import PlattCertificates.Count131072.C049618
import PlattCertificates.Count131072.C049619
import PlattCertificates.Count131072.C049620
import PlattCertificates.Count131072.C049621
import PlattCertificates.Count131072.C049622
import PlattCertificates.Count131072.C049623
import PlattCertificates.Count131072.C049624
import PlattCertificates.Count131072.C049625
import PlattCertificates.Count131072.C049626
import PlattCertificates.Count131072.C049627
import PlattCertificates.Count131072.C049628
import PlattCertificates.Count131072.C049629
import PlattCertificates.Count131072.C049630
import PlattCertificates.Count131072.C049631
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000300
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts49600 : List PrefixCut := [⟨64,250703015,250703160⟩]
theorem checked49600 : checkPrefixCuts (2^48) 6505103361 10 Manual.Count131072.C049600.packed 64 cuts49600 = true := by
 decide +kernel
def cuts49601 : List PrefixCut := [⟨30,119205492,119205556⟩,
⟨64,253337370,253337512⟩]
theorem checked49601 : checkPrefixCuts (2^48) 6505234433 10 Manual.Count131072.C049601.packed 64 cuts49601 = true := by
 decide +kernel
def pointBounds49601 : List (Nat × Nat × Nat) := [(6505295872,111557200030808,111557587096087)]
theorem point_links_checked49601 : (cuts49601.take 1).map (fun c => (6505234433-1+2*2^10*c.k,111557080825316+c.lower,111557467890531+c.upper)) = pointBounds49601 := by
 decide +kernel
def cuts49602 : List PrefixCut := [⟨64,248875696,248875837⟩]
theorem checked49602 : checkPrefixCuts (2^48) 6505365505 10 Manual.Count131072.C049602.packed 64 cuts49602 = true := by
 decide +kernel
def cuts49603 : List PrefixCut := [⟨2,8437110,8437114⟩,
⟨64,251553208,251553345⟩]
theorem checked49603 : checkPrefixCuts (2^48) 6505496577 10 Manual.Count131072.C049603.packed 64 cuts49603 = true := by
 decide +kernel
def pointBounds49603 : List (Nat × Nat × Nat) := [(6505500672,111557591475492,111557978540994)]
theorem point_links_checked49603 : (cuts49603.take 1).map (fun c => (6505496577-1+2*2^10*c.k,111557583038382+c.lower,111557970103880+c.upper)) = pointBounds49603 := by
 decide +kernel
def cuts49604 : List PrefixCut := [⟨38,150133418,150133505⟩,
⟨64,250812642,250812790⟩]
theorem checked49604 : checkPrefixCuts (2^48) 6505627649 10 Manual.Count131072.C049604.packed 64 cuts49604 = true := by
 decide +kernel
def pointBounds49604 : List (Nat × Nat × Nat) := [(6505705472,111557984725008,111558371790730)]
theorem point_links_checked49604 : (cuts49604.take 1).map (fun c => (6505627649-1+2*2^10*c.k,111557834591590+c.lower,111558221657225+c.upper)) = pointBounds49604 := by
 decide +kernel
def cuts49605 : List PrefixCut := [⟨64,251413257,251413401⟩]
theorem checked49605 : checkPrefixCuts (2^48) 6505758721 10 Manual.Count131072.C049605.packed 64 cuts49605 = true := by
 decide +kernel
def cuts49606 : List PrefixCut := [⟨10,39630334,39630355⟩,
⟨64,253398376,253398521⟩]
theorem checked49606 : checkPrefixCuts (2^48) 6505889793 10 Manual.Count131072.C049606.packed 64 cuts49606 = true := by
 decide +kernel
def pointBounds49606 : List (Nat × Nat × Nat) := [(6505910272,111558376447823,111558763513771)]
theorem point_links_checked49606 : (cuts49606.take 1).map (fun c => (6505889793-1+2*2^10*c.k,111558336817489+c.lower,111558723883416+c.upper)) = pointBounds49606 := by
 decide +kernel
def cuts49607 : List PrefixCut := [⟨46,181836260,181836364⟩,
⟨64,254258532,254258680⟩]
theorem checked49607 : checkPrefixCuts (2^48) 6506020865 10 Manual.Count131072.C049607.packed 64 cuts49607 = true := by
 decide +kernel
def pointBounds49607 : List (Nat × Nat × Nat) := [(6506115072,111558772052125,111559159118301)]
theorem point_links_checked49607 : (cuts49607.take 1).map (fun c => (6506020865-1+2*2^10*c.k,111558590215865+c.lower,111558977281937+c.upper)) = pointBounds49607 := by
 decide +kernel
def cuts49608 : List PrefixCut := [⟨64,252782467,252782613⟩]
theorem checked49608 : checkPrefixCuts (2^48) 6506151937 10 Manual.Count131072.C049608.packed 64 cuts49608 = true := by
 decide +kernel
def cuts49609 : List PrefixCut := [⟨18,72333883,72333925⟩,
⟨64,248970399,248970544⟩]
theorem checked49609 : checkPrefixCuts (2^48) 6506283009 10 Manual.Count131072.C049609.packed 64 cuts49609 = true := by
 decide +kernel
def pointBounds49609 : List (Nat × Nat × Nat) := [(6506319872,111559169590747,111559556657155)]
theorem point_links_checked49609 : (cuts49609.take 1).map (fun c => (6506283009-1+2*2^10*c.k,111559097256864+c.lower,111559484323230+c.upper)) = pointBounds49609 := by
 decide +kernel
def cuts49610 : List PrefixCut := [⟨54,210636722,210636842⟩,
⟨64,248922122,248922262⟩]
theorem checked49610 : checkPrefixCuts (2^48) 6506414081 10 Manual.Count131072.C049610.packed 64 cuts49610 = true := by
 decide +kernel
def pointBounds49610 : List (Nat × Nat × Nat) := [(6506524672,111559556863985,111559943930616)]
theorem point_links_checked49610 : (cuts49610.take 1).map (fun c => (6506414081-1+2*2^10*c.k,111559346227263+c.lower,111559733293774+c.upper)) = pointBounds49610 := by
 decide +kernel
def cuts49611 : List PrefixCut := [⟨64,249652496,249652642⟩]
theorem checked49611 : checkPrefixCuts (2^48) 6506545153 10 Manual.Count131072.C049611.packed 64 cuts49611 = true := by
 decide +kernel
def cuts49612 : List PrefixCut := [⟨26,100620945,100621000⟩,
⟨64,251204775,251204911⟩]
theorem checked49612 : checkPrefixCuts (2^48) 6506676225 10 Manual.Count131072.C049612.packed 64 cuts49612 = true := by
 decide +kernel
def pointBounds49612 : List (Nat × Nat × Nat) := [(6506729472,111559945422826,111560332489678)]
theorem point_links_checked49612 : (cuts49612.take 1).map (fun c => (6506676225-1+2*2^10*c.k,111559844801881+c.lower,111560231868678+c.upper)) = pointBounds49612 := by
 decide +kernel
def cuts49613 : List PrefixCut := [⟨62,243456609,243456748⟩,
⟨64,252108142,252108287⟩]
theorem checked49613 : checkPrefixCuts (2^48) 6506807297 10 Manual.Count131072.C049613.packed 64 cuts49613 = true := by
 decide +kernel
def pointBounds49613 : List (Nat × Nat × Nat) := [(6506934272,111560339463265,111560726530337)]
theorem point_links_checked49613 : (cuts49613.take 1).map (fun c => (6506807297-1+2*2^10*c.k,111560096006656+c.lower,111560483073589+c.upper)) = pointBounds49613 := by
 decide +kernel
def cuts49614 : List PrefixCut := [⟨64,254049648,254049792⟩]
theorem checked49614 : checkPrefixCuts (2^48) 6506938369 10 Manual.Count131072.C049614.packed 64 cuts49614 = true := by
 decide +kernel
def cuts49615 : List PrefixCut := [⟨34,131499916,131499990⟩,
⟨64,247772363,247772506⟩]
theorem checked49615 : checkPrefixCuts (2^48) 6507069441 10 Manual.Count131072.C049615.packed 64 cuts49615 = true := by
 decide +kernel
def pointBounds49615 : List (Nat × Nat × Nat) := [(6507139072,111560733664362,111561120731658)]
theorem point_links_checked49615 : (cuts49615.take 1).map (fun c => (6507069441-1+2*2^10*c.k,111560602164446+c.lower,111560989231668+c.upper)) = pointBounds49615 := by
 decide +kernel
def cuts49616 : List PrefixCut := [⟨64,249367814,249367959⟩]
theorem checked49616 : checkPrefixCuts (2^48) 6507200513 10 Manual.Count131072.C049616.packed 64 cuts49616 = true := by
 decide +kernel
def cuts49617 : List PrefixCut := [⟨6,25347430,25347444⟩,
⟨64,250271166,250271309⟩]
theorem checked49617 : checkPrefixCuts (2^48) 6507331585 10 Manual.Count131072.C049617.packed 64 cuts49617 = true := by
 decide +kernel
def pointBounds49617 : List (Nat × Nat × Nat) := [(6507343872,111561124652053,111561511719577)]
theorem point_links_checked49617 : (cuts49617.take 1).map (fun c => (6507331585-1+2*2^10*c.k,111561099304623+c.lower,111561486372133+c.upper)) = pointBounds49617 := by
 decide +kernel
def cuts49618 : List PrefixCut := [⟨42,163067134,163067228⟩,
⟨64,249703792,249703937⟩]
theorem checked49618 : checkPrefixCuts (2^48) 6507462657 10 Manual.Count131072.C049618.packed 64 cuts49618 = true := by
 decide +kernel
def pointBounds49618 : List (Nat × Nat × Nat) := [(6507548672,111561512642923,111561899710670)]
theorem point_links_checked49618 : (cuts49618.take 1).map (fun c => (6507462657-1+2*2^10*c.k,111561349575789+c.lower,111561736643442+c.upper)) = pointBounds49618 := by
 decide +kernel
def cuts49619 : List PrefixCut := [⟨64,251299135,251299279⟩]
theorem checked49619 : checkPrefixCuts (2^48) 6507593729 10 Manual.Count131072.C049619.packed 64 cuts49619 = true := by
 decide +kernel
def cuts49620 : List PrefixCut := [⟨14,55103470,55103502⟩,
⟨64,249564012,249564149⟩]
theorem checked49620 : checkPrefixCuts (2^48) 6507724801 10 Manual.Count131072.C049620.packed 64 cuts49620 = true := by
 decide +kernel
def pointBounds49620 : List (Nat × Nat × Nat) := [(6507753472,111561905682186,111562292750160)]
theorem point_links_checked49620 : (cuts49620.take 1).map (fun c => (6507724801-1+2*2^10*c.k,111561850578716+c.lower,111562237646658+c.upper)) = pointBounds49620 := by
 decide +kernel
def cuts49621 : List PrefixCut := [⟨50,195798253,195798367⟩,
⟨64,252067521,252067664⟩]
theorem checked49621 : checkPrefixCuts (2^48) 6507855873 10 Manual.Count131072.C049621.packed 64 cuts49621 = true := by
 decide +kernel
def pointBounds49621 : List (Nat × Nat × Nat) := [(6507958272,111562295940981,111562683009174)]
theorem point_links_checked49621 : (cuts49621.take 1).map (fun c => (6507855873-1+2*2^10*c.k,111562100142728+c.lower,111562487210807+c.upper)) = pointBounds49621 := by
 decide +kernel
def cuts49622 : List PrefixCut := [⟨64,251500218,251500363⟩]
theorem checked49622 : checkPrefixCuts (2^48) 6507986945 10 Manual.Count131072.C049622.packed 64 cuts49622 = true := by
 decide +kernel
def cuts49623 : List PrefixCut := [⟨22,87018325,87018376⟩,
⟨64,251754633,251754776⟩]
theorem checked49623 : checkPrefixCuts (2^48) 6508118017 10 Manual.Count131072.C049623.packed 64 cuts49623 = true := by
 decide +kernel
def pointBounds49623 : List (Nat × Nat × Nat) := [(6508163072,111562690728792,111563077797210)]
theorem point_links_checked49623 : (cuts49623.take 1).map (fun c => (6508118017-1+2*2^10*c.k,111562603710467+c.lower,111562990778834+c.upper)) = pointBounds49623 := by
 decide +kernel
def cuts49624 : List PrefixCut := [⟨58,227617110,227617235⟩,
⟨64,250711603,250711740⟩]
theorem checked49624 : checkPrefixCuts (2^48) 6508249089 10 Manual.Count131072.C049624.packed 64 cuts49624 = true := by
 decide +kernel
def pointBounds49624 : List (Nat × Nat × Nat) := [(6508367872,111563083082210,111563470150845)]
theorem point_links_checked49624 : (cuts49624.take 1).map (fun c => (6508249089-1+2*2^10*c.k,111562855465100+c.lower,111563242533610+c.upper)) = pointBounds49624 := by
 decide +kernel
def cuts49625 : List PrefixCut := [⟨64,255290805,255290949⟩]
theorem checked49625 : checkPrefixCuts (2^48) 6508380161 10 Manual.Count131072.C049625.packed 64 cuts49625 = true := by
 decide +kernel
def cuts49626 : List PrefixCut := [⟨30,117891310,117891382⟩,
⟨64,251912408,251912554⟩]
theorem checked49626 : checkPrefixCuts (2^48) 6508511233 10 Manual.Count131072.C049626.packed 64 cuts49626 = true := by
 decide +kernel
def pointBounds49626 : List (Nat × Nat × Nat) := [(6508572672,111563479358818,111563866427681)]
theorem point_links_checked49626 : (cuts49626.take 1).map (fun c => (6508511233-1+2*2^10*c.k,111563361467508+c.lower,111563748536299+c.upper)) = pointBounds49626 := by
 decide +kernel
def cuts49627 : List PrefixCut := [⟨64,251172163,251172303⟩]
theorem checked49627 : checkPrefixCuts (2^48) 6508642305 10 Manual.Count131072.C049627.packed 64 cuts49627 = true := by
 decide +kernel
def cuts49628 : List PrefixCut := [⟨2,7351726,7351730⟩,
⟨64,253199595,253199739⟩]
theorem checked49628 : checkPrefixCuts (2^48) 6508773377 10 Manual.Count131072.C049628.packed 64 cuts49628 = true := by
 decide +kernel
def pointBounds49628 : List (Nat × Nat × Nat) := [(6508777472,111563871903805,111564258972886)]
theorem point_links_checked49628 : (cuts49628.take 1).map (fun c => (6508773377-1+2*2^10*c.k,111563864552079+c.lower,111564251621156+c.upper)) = pointBounds49628 := by
 decide +kernel
def cuts49629 : List PrefixCut := [⟨38,147765889,147765972⟩,
⟨64,249648508,249648648⟩]
theorem checked49629 : checkPrefixCuts (2^48) 6508904449 10 Manual.Count131072.C049629.packed 64 cuts49629 = true := by
 decide +kernel
def pointBounds49629 : List (Nat × Nat × Nat) := [(6508982272,111564265517563,111564652586867)]
theorem point_links_checked49629 : (cuts49629.take 1).map (fun c => (6508904449-1+2*2^10*c.k,111564117751674+c.lower,111564504820895+c.upper)) = pointBounds49629 := by
 decide +kernel
def cuts49630 : List PrefixCut := [⟨64,251978623,251978768⟩]
theorem checked49630 : checkPrefixCuts (2^48) 6509035521 10 Manual.Count131072.C049630.packed 64 cuts49630 = true := by
 decide +kernel
def cuts49631 : List PrefixCut := [⟨10,39437415,39437438⟩,
⟨64,253616748,253616887⟩]
theorem checked49631 : checkPrefixCuts (2^48) 6509166593 10 Manual.Count131072.C049631.packed 64 cuts49631 = true := by
 decide +kernel
def pointBounds49631 : List (Nat × Nat × Nat) := [(6509187072,111564658816220,111565045885749)]
theorem point_links_checked49631 : (cuts49631.take 1).map (fun c => (6509166593-1+2*2^10*c.k,111564619378805+c.lower,111565006448311+c.upper)) = pointBounds49631 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000300
