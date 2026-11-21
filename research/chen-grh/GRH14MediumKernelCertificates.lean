import GRH14LowerFactor

noncomputable section
namespace ChenEffective.GRH14
open Real Finset
set_option maxHeartbeats 12000000
set_option maxRecDepth 8192

def mediumCellStart (i : Fin 64) : ℝ := 1/10+(7/1920:ℝ)*i.val
def mediumCellRatio (i : Fin 64) : ℝ := 5-10*(mediumCellStart i+7/1920)-(71/1000:ℝ)
def mediumKernelCell (i : Fin 64) : ℝ := (7/1920:ℝ)/(mediumCellStart i*(mediumCellRatio i)^2)
def mediumExpPolynomial (u : ℝ) : ℝ := 1+u+u^2/2+u^3/6+u^4/24+u^5/120+u^6/720
def mediumHatEnvelope (s : ℝ) : ℝ :=
  if s ≤ 2 then 1 else if s ≤ 3 then 1/mediumExpPolynomial (s-2) else (3/s)/mediumExpPolynomial (s-2)
def mediumHatCell (i : Fin 64) : ℝ := (7/1920:ℝ)*mediumHatEnvelope (mediumCellRatio i)/mediumCellStart i
def mediumKernelCaps : Fin 64 → ℕ := ![240620,236566,232911,229619,226661,224010,221643,219541,217686,216064,214660,213463,212463,211651,211019,210561,210270,210142,210173,210359,210698,211187,211825,212611,213545,214627,215858,217238,218769,220455,222296,224297,226461,228793,231297,233979,236844,239900,243154,246614,250289,254188,258323,262705,267346,272262,277465,282974,288806,294981,301520,308447,315787,323569,331824,340585,349890,359780,370300,381502,393439,406174,419776,434321]
def mediumHatCaps : Fin 64 → ℕ := ![424847,428997,433775,439164,445152,451733,458900,466655,474997,483932,493467,503610,514374,525770,537816,550528,563927,578033,592871,608467,624848,642044,660088,679015,698862,715131,727791,740937,754578,768721,783376,798554,814266,830523,847337,864721,882689,901254,920432,940238,960688,981798,1003587,1026072,1049273,1073209,1097900,1123367,1149633,1176720,1204651,1233451,1258993,1243340,1228071,1213172,1198631,1184434,1170569,1157025,1143791,1130857,1118211,1105846]

theorem medium_kernel_cell_certificate (i : Fin 64) :
    mediumKernelCell i  ≤  (mediumKernelCaps i:ℝ)/100000000 := by
  fin_cases i <;> norm_num [mediumKernelCell,mediumCellStart,mediumCellRatio,mediumKernelCaps]

theorem medium_hat_cell_certificate (i : Fin 64) :
    mediumHatCell i  ≤  (mediumHatCaps i:ℝ)/100000000 := by
  fin_cases i <;> norm_num [mediumHatCell,mediumCellStart,mediumCellRatio,
    mediumHatEnvelope,mediumExpPolynomial,mediumHatCaps]

theorem medium_kernel_grid_certificate : (∑ i : Fin 64, mediumKernelCell i)  ≤  (1661/10000:ℝ) := by
  have hh := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin 64))) => medium_kernel_cell_certificate i)
  apply hh.trans
  norm_num [mediumKernelCaps,Fin.sum_univ_succ]

theorem medium_hat_grid_certificate : (∑ i : Fin 64, mediumHatCell i)  ≤  (53/100:ℝ) := by
  have hh := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin 64))) => medium_hat_cell_certificate i)
  apply hh.trans
  norm_num [mediumHatCaps,Fin.sum_univ_succ]

#print axioms medium_kernel_grid_certificate
#print axioms medium_hat_grid_certificate
end ChenEffective.GRH14
