import PlattPointSubsetKernel
import PlattPointPackets.S1B000505
import PlattPointPackets.S1B000506
import PlattPointPackets.S1B000507
import PlattPointPackets.S1B000508
import PlattPointPackets.S1B000509
import PlattGlobalGrid.S6B000067
namespace ChenEffective.PlattWindow.PointCovers.S6B000067
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S1B000505.points ++ ChenEffective.PlattWindow.PointPackets.S1B000506.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000507.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000508.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000509.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000067.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000067.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000067
