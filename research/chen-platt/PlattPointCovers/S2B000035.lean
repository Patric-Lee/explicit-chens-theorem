import PlattPointSubsetKernel
import PlattPointPackets.S1B000022
import PlattPointPackets.S1B000023
import PlattGlobalGrid.S2B000035
namespace ChenEffective.PlattWindow.PointCovers.S2B000035
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (ChenEffective.PlattWindow.PointPackets.S1B000022.points ++ ChenEffective.PlattWindow.PointPackets.S1B000023.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S2B000035.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S2B000035.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S2B000035
