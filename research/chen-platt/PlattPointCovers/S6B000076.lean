import PlattPointSubsetKernel
import PlattPointPackets.S1B000542
import PlattPointPackets.S1B000543
import PlattPointPackets.S1B000544
import PlattPointPackets.S1B000545
import PlattPointPackets.S1B000546
import PlattGlobalGrid.S6B000076
namespace ChenEffective.PlattWindow.PointCovers.S6B000076
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S1B000542.points ++ ChenEffective.PlattWindow.PointPackets.S1B000543.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000544.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000545.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000546.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000076.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000076.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000076
