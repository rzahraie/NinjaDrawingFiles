#region Using declarations
 using System;
 using System.Collections.Generic;
 using System.ComponentModel;
 using System.ComponentModel.DataAnnotations;
 using System.Linq;
 using System.Windows;
 using System.Windows.Controls;
 using System.Windows.Input;
 using System.Windows.Media;
 using System.Xml.Serialization;
 using NinjaTrader.Cbi;
 using NinjaTrader.Gui;
 using NinjaTrader.Gui.Chart;
 using NinjaTrader.Core.FloatingPoint;
 using NinjaTrader.Gui.Tools;
 using NinjaTrader.Data;
 using NinjaTrader.NinjaScript;
 using SharpDX.DirectWrite;
 #endregion
 
 //This namespace holds Drawing tools in this folder and is required. Do not change it. 
 namespace NinjaTrader.NinjaScript.DrawingTools
 { 
	 public struct Seg {
	 public readonly int SIdx, EIdx; 
	 public readonly double SY, EY; 
	 public Seg(int sidx, double sy, int eidx, double ey) {
	 SIdx = sidx;
	 EIdx = eidx;
	 SY = sy;
	 EY = ey;
	 }
 }
 
 public enum BreakMode
 {
	 HighLowPenetration, // bar’s high/low crosses the RTL
	 CloseCross // bar’s close crosses the RTL
 }
 
 public class CustomLine : DrawingTool
 {
 /// <summary>
 /// portable dash mode (names match Ninja's enum and WPF styles)
 /// </summary>
 private enum DashMode { Solid, Dash, Dot, DashDot, DashDotDot }
 
 // order to rotate through when pressing Ctrl+Q
 private static readonly DashMode[] _dashCycleModes =
 {
 DashMode.Solid, DashMode.Dash, DashMode.Dot, DashMode.DashDot, DashMode.DashDotDot
 };
 
 private const double cursorSensitivity = 15;
 private ChartAnchor editingAnchor;
 
 /// <summary>
 /// Container/line properties
 /// </summary>
 private bool isUpContainer = true;
 private double lineSlope = 0.0;
 private double rtlEndPointPrice = 0.0;
 private int rtlEndPointX = 0;
 
 private bool _invalidatePending;
 
 
 private readonly List<Seg> segments = new List<Seg>();
 private bool _isExtending;
 
 /// <summary>
 /// Snap rectangle properties
 /// </summary>
 private SharpDX.RectangleF? _snapRectDx = null;
 private const float _snapSizePx = 12f; // square size
 private const double _snapYTolPx = 8.0; // vertical tolerance
 private const int _snapLookaround = 1; 
 private Point? hoverHitPx = null;
 private const double hoverTolPx = 5; // pixel tolerance
 private int anchorPanelIndex = 0;
 
 /// <summary>
 /// Context Menu properties
 /// </summary>
 private MenuItem menuItem1;
 private MenuItem menuItem2;
 private MenuItem menuItemNumbers;
 private MenuItem menuItemStyle;
 private ChartControl activeChartControl;
 private KeyEventHandler previewKeyDownHandler;
 private KeyEventHandler windowPreviewKeyDownHandler;
 private ContextMenuEventHandler contextMenuOpeningHandler;
 private ContextMenuEventHandler contextMenuClosingHandler;
 private readonly RoutedCommand extendCommand = new RoutedCommand();
 private CommandBinding extendCommandBinding;
 private CommandBinding extendCommandBindingWin;
 private bool _recalcAfterReloadTried = false;
 private Window activeChartWindow;
 private ChartScale _lastChartScale = null;
 
 /// <summary>
 /// Channel numbers (i.e. points 1,2,3)
 /// </summary>
 private bool _showNumbers = false;
 private int? _lastSIdx;
 private int? _lastEIdx;
 private int? _lastP2Idx; 
 private int? _lastP3Idx;
 private double _lastSlope;
 
 // cached after first click; NEVER change these again
	private int    startBar;                  // freeze this
	decimal startPriceDec;            // freeze this (already tick-rounded)
	bool   startFrozen;
 
 
 /// <summary>
 /// Auto-extend timer state
 /// </summary>
 private System.Windows.Threading.DispatcherTimer _autoTimer;
 private bool _autoRunning;
 private bool _hotkeyGate; // debounces duplicate window/control key events
 
 /// <summary>
 /// Keep P2 only for the current recompute (drag, Ctrl+R, or auto-extend)
 /// </summary>
 private bool _keepP2ThisPass = false;
 
 private const float MinWidth = 1f;
 private const float MaxWidth = 12f;
 private const float StepWidth = 1f;
 
 /// <summary>
 /// KeyBindings for Ctrl+R (extend)
 /// </summary>
 private KeyBinding keyBindingCtrlR_Control;
 private KeyBinding keyBindingCtrlR_Window;
 
private int? _lastPublishedP2Idx = null;
private int? _lastPublishedP3Idx = null;
private double? _lastPublishedP2Price = null;
private double? _lastPublishedP3Price = null;
private int? _lastPublishedEndIdx = null;
private double? _lastPublishedEndPrice = null;
private int? _lastPublishedAnalysisEndIdx = null;
private int? _lastPublishedCandidateBar = null;
private int? _lastPublishedConfirmedBar = null;
private int? _lastPublishedFlipCount = null;
private int? _lastPublishedVolCount = null;
private string _lastPublishedSignal = null;
private bool _publishInProgress = false;

private bool ShouldPublishManualAnalysis(
    NinjaTrader.NinjaScript.xPva.Engine.ManualContainerAnalysis analysis,
    string signal)
{
    int analysisEndIdx = analysis.Snapshot.AnalysisEndBarIndex;
    int? candidateBar = analysis.FttCandidateBar;
    int? confirmedBar = analysis.FttConfirmedBar;
    int flipCount = analysis.VolumeSequence.FlipCount;
    int volCount = analysis.VolumeEvents != null ? analysis.VolumeEvents.Length : 0;

    bool same =
        _lastPublishedAnalysisEndIdx.HasValue &&
        _lastPublishedCandidateBar == candidateBar &&
        _lastPublishedConfirmedBar == confirmedBar &&
        _lastPublishedFlipCount.HasValue &&
        _lastPublishedVolCount.HasValue &&
        _lastPublishedSignal != null &&
        _lastPublishedAnalysisEndIdx.Value == analysisEndIdx &&
        _lastPublishedFlipCount.Value == flipCount &&
        _lastPublishedVolCount.Value == volCount &&
        _lastPublishedSignal == signal;

    if (same)
        return false;

    _lastPublishedAnalysisEndIdx = analysisEndIdx;
    _lastPublishedCandidateBar = candidateBar;
    _lastPublishedConfirmedBar = confirmedBar;
    _lastPublishedFlipCount = flipCount;
    _lastPublishedVolCount = volCount;
    _lastPublishedSignal = signal;

    return true;
} 
 
private bool ShouldPublishManualSnapshot(
    NinjaTrader.NinjaScript.xPva.Engine.ManualContainerSnapshot snapshot)
{
    int currentEndIdx = _lastEIdx ?? rtlEndPointX;
    double currentEndPrice = rtlEndPointPrice;

    bool same =
        _lastPublishedP2Idx.HasValue &&
        _lastPublishedP3Idx.HasValue &&
        _lastPublishedP2Price.HasValue &&
        _lastPublishedP3Price.HasValue &&
        _lastPublishedEndIdx.HasValue &&
        _lastPublishedEndPrice.HasValue &&
        _lastPublishedP2Idx.Value == snapshot.P2.BarIndex &&
        _lastPublishedP3Idx.Value == snapshot.P3.BarIndex &&
        _lastPublishedP2Price.Value == snapshot.P2.Price &&
        _lastPublishedP3Price.Value == snapshot.P3.Price &&
        _lastPublishedEndIdx.Value == currentEndIdx &&
        _lastPublishedEndPrice.Value == currentEndPrice;

    if (same)
        return false;

    _lastPublishedP2Idx = snapshot.P2.BarIndex;
    _lastPublishedP3Idx = snapshot.P3.BarIndex;
    _lastPublishedP2Price = snapshot.P2.Price;
    _lastPublishedP3Price = snapshot.P3.Price;
    _lastPublishedEndIdx = currentEndIdx;
    _lastPublishedEndPrice = currentEndPrice;

    return true;
}


private void PublishManualSnapshotIfReady(ChartControl chartControl, ChartBars chartBars)
{
    if (_publishInProgress)
        return;

    _publishInProgress = true;

    try
    {
        var snapshot = BuildManualContainerSnapshot(chartControl, chartBars);
        if (!snapshot.HasValue)
            return;

        if (!ShouldPublishManualSnapshot(snapshot.Value))
            return;

        var analysis =
            NinjaTrader.NinjaScript.xPva.Engine.xPvaManualContainerAnalyzer.Analyze(
                snapshot.Value,
                idx => chartBars.Bars.GetOpen(idx),
                idx => chartBars.Bars.GetHigh(idx),
                idx => chartBars.Bars.GetLow(idx),
                idx => chartBars.Bars.GetClose(idx),
                idx => (long)chartBars.Bars.GetVolume(idx),
                chartBars.Bars.Instrument.MasterInstrument.TickSize);

        bool mixed = analysis.VolumeSequence.IsMixed;
        bool domShift = analysis.VolumeSequence.HasDominantShift;
        bool ndReturn = analysis.VolumeSequence.HasNonDominantReturn;
        int flipCount = analysis.VolumeSequence.FlipCount;

        bool isTradable =
            flipCount <= 3 &&
            !mixed &&
            (domShift || !ndReturn);

        string signal = "SKIP";

        if (isTradable && analysis.FttConfirmedBar.HasValue)
            signal = analysis.Snapshot.IsUpContainer ? "LONG" : "SHORT";

        if (!ShouldPublishManualAnalysis(analysis, signal))
            return;

        Print($"[CustomLine] startFrozen={startFrozen} p2={_lastP2Idx} p3={_lastP3Idx} up={isUpContainer}");
        PrintManualContainerSnapshot(snapshot.Value);

        Print($"[ManualAnalysis] C#{analysis.Snapshot.ContainerId} volCount={analysis.VolumeEvents.Length}");
        if (analysis.FttCandidateBar.HasValue)
            Print($"[ManualAnalysis] Candidate={analysis.FttCandidateBar.Value}");
        if (analysis.FttConfirmedBar.HasValue)
            Print($"[ManualAnalysis] Confirmed={analysis.FttConfirmedBar.Value}");
        if (analysis.StructureState.HasValue)
            Print($"[ManualAnalysis] Structure={analysis.StructureState.Value}");
        if (analysis.ActionType.HasValue)
            Print($"[ManualAnalysis] Action={analysis.ActionType.Value}");
        if (analysis.TradeIntent.HasValue)
            Print($"[ManualAnalysis] TradeIntent={analysis.TradeIntent.Value}");

        for (int i = 0; i < analysis.VolumeEvents.Length; i++)
        {
            var ve = analysis.VolumeEvents[i];
            Print($"[ManualAnalysis] Vol {ve.Label} bar={ve.BarIndex} vol={ve.Volume} pol={ve.Polarity} dom={ve.Dominance}");
        }

        Print($"[ManualAnalysis] Seq {analysis.VolumeSequence.SequenceText}");
        Print($"[ManualAnalysis] SeqFlags domShift={analysis.VolumeSequence.HasDominantShift} ndReturn={analysis.VolumeSequence.HasNonDominantReturn} mixed={analysis.VolumeSequence.IsMixed}");
        Print($"[ManualAnalysis] VolState={analysis.VolumeState}");
        Print($"[ManualAnalysis] FlipCount={analysis.VolumeSequence.FlipCount}");

        Print(
            $"[ManualSignal] C#{analysis.Snapshot.ContainerId} " +
            $"Signal={signal} " +
            $"Confirmed={(analysis.FttConfirmedBar.HasValue ? analysis.FttConfirmedBar.Value.ToString() : "None")} " +
            $"Flip={flipCount} Mixed={mixed} DomShift={domShift} NDReturn={ndReturn}");

        NinjaTrader.NinjaScript.xPva.Engine.xPvaManualContainerBridge.Publish(analysis);
    }
    finally
    {
        _publishInProgress = false;
    }
}

private NinjaTrader.NinjaScript.xPva.Engine.ManualContainerSnapshot? BuildManualContainerSnapshot(
    ChartControl chartControl,
    ChartBars chartBars)
{
    if (!startFrozen)
        return null;

    if (!_lastP2Idx.HasValue || !_lastP3Idx.HasValue)
        return null;

	int p1Idx = startBar;
	int p2Idx = _lastP2Idx.Value;
	int p3Idx = _lastP3Idx.Value;
	
	// Repair degenerate P2 when the tool reports P1 == P2.
	// For up containers, choose the highest high between P1 and P3.
	// For down containers, choose the lowest low between P1 and P3.
	if (p2Idx <= p1Idx && p3Idx > p1Idx)
	{
	    int repairedP2 = p1Idx;
	
	    if (isUpContainer)
	    {
	        double bestHigh = chartBars.Bars.GetHigh(p1Idx);
	
	        for (int i = p1Idx + 1; i <= p3Idx; i++)
	        {
	            double h = chartBars.Bars.GetHigh(i);
	            if (h > bestHigh)
	            {
	                bestHigh = h;
	                repairedP2 = i;
	            }
	        }
	    }
	    else
	    {
	        double bestLow = chartBars.Bars.GetLow(p1Idx);
	
	        for (int i = p1Idx + 1; i <= p3Idx; i++)
	        {
	            double l = chartBars.Bars.GetLow(i);
	            if (l < bestLow)
	            {
	                bestLow = l;
	                repairedP2 = i;
	            }
	        }
	    }
	
	    p2Idx = repairedP2;
	}
	
	if (!(p1Idx < p2Idx && p2Idx < p3Idx))
	{
	    Print($"[CustomLine-BadOrder] p1={p1Idx} p2={p2Idx} p3={p3Idx}");
	    return null;
	}

    double p1Price = (double)startPriceDec;
    double p2Price = GetPriceAtBar(chartBars, p2Idx, isUpContainer ? true : false);
    double p3Price = GetPriceAtBar(chartBars, p3Idx, isUpContainer ? false : true);

    if (p3Idx == p1Idx)
        return null;

    double rtlSlope = (p3Price - p1Price) / (double)(p3Idx - p1Idx);

    // LTL is parallel to RTL and passes through P2
    double ltlSlope = rtlSlope;

    var breakMode =
    ExtendBreakRule == BreakMode.CloseCross
        ? NinjaTrader.NinjaScript.xPva.Engine.ManualContainerBreakMode.CloseCross
        : NinjaTrader.NinjaScript.xPva.Engine.ManualContainerBreakMode.HighLowPenetration;
	
	int analysisEndIdx = _lastEIdx ?? rtlEndPointX;
	double analysisEndPrice = rtlEndPointPrice;

	return new NinjaTrader.NinjaScript.xPva.Engine.ManualContainerSnapshot(
	    containerId: p1Idx,
	    isUpContainer: isUpContainer,
	    p1: new NinjaTrader.NinjaScript.xPva.Engine.ManualContainerPoint(p1Idx, p1Price),
	    p2: new NinjaTrader.NinjaScript.xPva.Engine.ManualContainerPoint(p2Idx, p2Price),
	    p3: new NinjaTrader.NinjaScript.xPva.Engine.ManualContainerPoint(p3Idx, p3Price),
	    rtlSlope: rtlSlope,
	    ltlSlope: ltlSlope,
	    breakMode: breakMode,
	    breakToleranceTicks: 0.0,
		analysisEndBarIndex: analysisEndIdx,
    	analysisEndPrice: analysisEndPrice);
}

private void PrintManualContainerSnapshot(
    NinjaTrader.NinjaScript.xPva.Engine.ManualContainerSnapshot snapshot)
{
    Print(string.Format(
        "ManualContainer C#{0} dir={1} P1=({2},{3}) P2=({4},{5}) P3=({6},{7}) rtlSlope={8} ltlSlope={9}",
        snapshot.ContainerId,
        snapshot.IsUpContainer ? "Up" : "Down",
        snapshot.P1.BarIndex,
        snapshot.P1.Price,
        snapshot.P2.BarIndex,
        snapshot.P2.Price,
        snapshot.P3.BarIndex,
        snapshot.P3.Price,
        snapshot.RtlSlope,
        snapshot.LtlSlope));
}

private void PublishManualAnalysisIfReady(ChartControl chartControl, ChartBars chartBars)
{
    var snapshot = BuildManualContainerSnapshot(chartControl, chartBars);
    if (!snapshot.HasValue)
        return;

    if (!ShouldPublishManualSnapshot(snapshot.Value))
        return;

	Print($"[CustomLine-IdxRaw] startBar={startBar} p2={_lastP2Idx} p3={_lastP3Idx}");
	Print($"[CustomLine-IdxFixed] p1={snapshot.Value.P1.BarIndex} p2={snapshot.Value.P2.BarIndex} p3={snapshot.Value.P3.BarIndex}");
    Print($"[CustomLine] startFrozen={startFrozen} p2={_lastP2Idx} p3={_lastP3Idx} up={isUpContainer}");
    PrintManualContainerSnapshot(snapshot.Value);

    var analysis =
	    NinjaTrader.NinjaScript.xPva.Engine.xPvaManualContainerAnalyzer.Analyze(
	        snapshot.Value,
	        idx => chartBars.Bars.GetOpen(idx),
	        idx => chartBars.Bars.GetHigh(idx),
	        idx => chartBars.Bars.GetLow(idx),
	        idx => chartBars.Bars.GetClose(idx),
	        idx => (long)chartBars.Bars.GetVolume(idx),
	        chartBars.Bars.Instrument.MasterInstrument.TickSize);

    NinjaTrader.NinjaScript.xPva.Engine.xPvaManualContainerBridge.Publish(analysis);
}

private double GetPriceAtBar(ChartBars chartBars, int barIdx, bool useHigh)
{
    if (chartBars == null || chartBars.Bars == null)
        return 0.0;

    if (barIdx < 0 || barIdx >= chartBars.Bars.Count)
        return 0.0;

    return useHigh
        ? chartBars.Bars.GetHigh(barIdx)
        : chartBars.Bars.GetLow(barIdx);
}

 private void RequestRepaint(ChartControl cc)
{
    if (cc == null || _invalidatePending) return;
    _invalidatePending = true;
    cc.Dispatcher.BeginInvoke(new Action(() =>
    {
        _invalidatePending = false;
        cc.InvalidateVisual();
    }), System.Windows.Threading.DispatcherPriority.Render);
}

// decimal tick rounding stays the same
static decimal RoundToTick(decimal price, decimal tick)
{
    return Math.Round(price / tick, 0, MidpointRounding.AwayFromZero) * tick;
}

// compute Y for any bar without touching X/Time (unchanged)
decimal PriceAtBar(int bar, decimal slopePerBar)
{
    return startPriceDec + slopePerBar * (bar - startBar);
}

// NEW signature: take ChartBars; derive index and instrument internally
void FreezeStartAnchor(ChartAnchor a, ChartControl cc, ChartBars cb)
{
    if (startFrozen || a == null || cb == null || cc == null) return;

    // Floor the start index to the bar at/before the anchor time
    int idx = IndexAtOrBefore(cb, cc, a.Time);
    if (idx < 0) idx = 0;

    startBar      = idx;
    startPriceDec = (decimal)a.Price;

    var instr = cb.Bars?.Instrument;  // NinjaTrader.Cbi.Instrument
    if (instr != null)
    {
        var tickDec = (decimal)instr.MasterInstrument.TickSize;
        startPriceDec = RoundToTick(startPriceDec, tickDec);
        a.Price = (double)startPriceDec; // snap only Y
    }

    startFrozen = true;
	
	_lastPublishedP2Idx = null;
	_lastPublishedP3Idx = null;
	_lastPublishedP2Price = null;
	_lastPublishedP3Price = null;
	_lastPublishedEndIdx = null;
	_lastPublishedEndPrice = null;
	_lastPublishedAnalysisEndIdx = null;
	_lastPublishedCandidateBar = null;
	_lastPublishedConfirmedBar = null;
	_lastPublishedFlipCount = null;
	_lastPublishedVolCount = null;
	_lastPublishedSignal = null;
}


// When user moves/commits the second point (or while previewing):
void UpdateEndAnchor(ChartAnchor end, int endBar, Instrument instr)
{
    var tickDec = (decimal)instr.MasterInstrument.TickSize;

    // slope in price-per-bar computed in decimal
    decimal endPriceDec = (decimal)end.Price;
    decimal slope       = (endPriceDec - startPriceDec) / (endBar - startBar);

    // project end price for its exact bar and snap ONLY price
    endPriceDec = RoundToTick(PriceAtBar(endBar, slope), tickDec);

    end.Price = (double)endPriceDec; // DO NOT set end.Time from price
}

 private void ChartControl_ContextMenuClosing(object sender, ContextMenuEventArgs e)
 {
 if (activeChartControl?.ContextMenu != null)
 {
 var items = activeChartControl.ContextMenu.Items;
 if (menuItem1 != null && items.Contains(menuItem1)) items.Remove(menuItem1);
 if (menuItem2 != null && items.Contains(menuItem2)) items.Remove(menuItem2);
 if (menuItemNumbers != null && items.Contains(menuItemNumbers)) items.Remove(menuItemNumbers);
 if (menuItemStyle != null && items.Contains(menuItemStyle)) items.Remove(menuItemStyle);
 }
 }
 
 private void ChartControl_ContextMenuOpening(object sender, ContextMenuEventArgs e)
 {
 if (!IsSelected || activeChartControl?.ContextMenu == null) return;
 
 var items = activeChartControl.ContextMenu.Items;
 if (menuItem1 != null && !items.Contains(menuItem1)) items.Add(menuItem1);
 if (menuItem2 != null && !items.Contains(menuItem2)) items.Add(menuItem2);
 if (menuItemNumbers != null)
 {
 menuItemNumbers.IsChecked = _showNumbers; // keep its visual in sync
 if (!items.Contains(menuItemNumbers)) items.Add(menuItemNumbers);
 }
 if (menuItemStyle != null && !items.Contains(menuItemStyle)) items.Add(menuItemStyle);
 
 
 }
 
 public override IEnumerable<ChartAnchor> Anchors
 {
 get
 {
 if (StartAnchor != null) yield return StartAnchor;
 if (EndAnchor != null) yield return EndAnchor;
 if (VeStartAnchor != null) yield return VeStartAnchor;
 if (VeEndAnchor != null) yield return VeEndAnchor;
 }
 }
 
 [Browsable(true)]
 [Display(ResourceType = typeof(Custom.Resource), Name = "Channel Line Properties", GroupName = "Lines", Order = 1)]
 public Stroke LineStroke { get; set; }
 
 [Display(Order = 1)]
 public ChartAnchor StartAnchor { get; set; }
 
 [Display(Order = 2)]
 public ChartAnchor EndAnchor { get; set; }
 
 [Display(Order = 3)]
 public ChartAnchor VeStartAnchor { get; set; }
 
 [Display(Order = 4)]
 public ChartAnchor VeEndAnchor { get; set; }
 
 [XmlIgnore]
 [Display(Name="Up Channel line Color",GroupName = "Lines",Order = 2)]
 public System.Windows.Media.Brush UpBrush {get; set;}
 
 [Browsable(false)]
 public string UpBrushSerialize
 {
 get => Serialize.BrushToString(UpBrush);
 set => UpBrush = Serialize.StringToBrush(value);
 }
 
 [XmlIgnore]
 [Display(Name="Down Channel line Color",GroupName = "Lines",Order = 3)]
 public System.Windows.Media.Brush DownBrush {get; set;}
 
 [Browsable(false)]
 public string DownBrushSerialize
 {
 get => Serialize.BrushToString(DownBrush);
 set => DownBrush = Serialize.StringToBrush(value);
 }
 
 [Category("Extend"), Display(Name="Auto-extend latest container", Order=5)]
 public bool AutoExtend { get; set; }
 
 [Category("Extend"), Display(Name="Break rule", Order=6)]
 public BreakMode ExtendBreakRule { get; set; }
 
 [Category("Display"), Display(Name="Show Numbers", Order=7)]
 public bool ShowNumbers { get => _showNumbers; set { _showNumbers = value; } }
 
 [Category("Extend"), Display(Name="Auto-extend interval (ms)", Order=8)]
 public int AutoExtendIntervalMs { get; set; }
 
 // ===================== Debug printing =====================
 [Category("Debug"), Display(Name = "Enable debug logs", Order = 9)]
 public bool DebugLogs { get; set; } // shows up in the UI so you can toggle at runtime
 
 private void PrintDebug(string message)
 {
 if (DebugLogs)
 PrintDebug($"[CustomLine] {message}");
 }
 
 // (Optional) use this overload when building expensive strings:
 // PrintDebug(() => $"Heavy {obj.Expensive()} formatting");
 private void PrintDebug(Func<string> messageFactory)
 {
 if (DebugLogs)
 PrintDebug($"[CustomLine] {messageFactory()}");
 }
 
 private void PrintDebugEx(Func<string> messageFactory)
 {
 if (DebugLogs)
 PrintDebug(messageFactory());
 }
 // ==========================================================
 
 public override bool SupportsAlerts { get { return true; } }
 
 public override IEnumerable<AlertConditionItem> GetAlertConditionItems()
 {
 yield return new AlertConditionItem 
 {
 Name = "CustomLine",
 ShouldOnlyDisplayName = true,
 };
 }
 
 // WPF DashStyle mapping
 private static DashStyle ToWpfDash(DashMode m) =>
 m == DashMode.Solid ? DashStyles.Solid :
 m == DashMode.Dash ? DashStyles.Dash :
 m == DashMode.Dot ? DashStyles.Dot :
 m == DashMode.DashDot ? DashStyles.DashDot :
 DashStyles.DashDotDot;
 
 private DashMode GetCurrentDashMode()
 {
 if (LineStroke == null) return DashMode.Solid;
 
 // Ninja first: Stroke.DashStyleHelper
 var pHelper = typeof(Stroke).GetProperty("DashStyleHelper");
 if (pHelper != null)
 {
 var val = pHelper.GetValue(LineStroke);
 if (val != null && Enum.TryParse(val.ToString(), out DashMode m))
 return m;
 }
 
 // WPF: Stroke.DashStyle
 var pDash = typeof(Stroke).GetProperty("DashStyle");
 if (pDash != null)
 {
 var ds = pDash.GetValue(LineStroke) as DashStyle;
 if (ds == DashStyles.Solid) return DashMode.Solid;
 if (ds == DashStyles.Dash) return DashMode.Dash;
 if (ds == DashStyles.Dot) return DashMode.Dot;
 if (ds == DashStyles.DashDot) return DashMode.DashDot;
 if (ds == DashStyles.DashDotDot)return DashMode.DashDotDot;
 }
 
 return DashMode.Solid;
 }
 
 private void ApplyDash(DashMode mode)
 {
 if (LineStroke == null) return;
 
 // Ninja property if present
 var pHelper = typeof(Stroke).GetProperty("DashStyleHelper");
 if (pHelper != null)
 {
 var enumVal = Enum.Parse(pHelper.PropertyType, mode.ToString());
 pHelper.SetValue(LineStroke, enumVal);
 //DeferInvalidate(activeChartControl ?? ChartPanel?.ChartControl);
	 RequestRepaint(activeChartControl ?? ChartPanel?.ChartControl);
 return;
 }
 
 // WPF property if present
 var pDash = typeof(Stroke).GetProperty("DashStyle");
 if (pDash != null)
 {
 pDash.SetValue(LineStroke, ToWpfDash(mode));
 //DeferInvalidate(activeChartControl ?? ChartPanel?.ChartControl);
	 RequestRepaint(activeChartControl ?? ChartPanel?.ChartControl);
 }
 }
 
 private void CycleLineStyle()
 {
 var current = GetCurrentDashMode();
 int idx = Array.IndexOf(_dashCycleModes, current);
 if (idx < 0) idx = 0;
 idx = (idx + 1) % _dashCycleModes.Length;
 ApplyDash(_dashCycleModes[idx]);
 PrintDebug($"Dash style -> {_dashCycleModes[idx]}");
 }
 
 private void AdjustLineWidth(float delta)
 {
 if (LineStroke == null) return;
 float nw = LineStroke.Width + delta;
 if (nw < MinWidth) nw = MinWidth;
 if (nw > MaxWidth) nw = MaxWidth;
 if (Math.Abs(nw - LineStroke.Width) > float.Epsilon)
 {
 LineStroke.Width = nw;
 PrintDebug($"Line width -> {LineStroke.Width}");
 //DeferInvalidate(activeChartControl ?? ChartPanel?.ChartControl);
	 RequestRepaint(activeChartControl ?? ChartPanel?.ChartControl);
 }
 }
 
 private bool HandleStyleWidthHotkeys(KeyEventArgs e)
 {
 if (!IsSelected) return false;
 
 // Ctrl+Q → cycle dash style
 if (Keyboard.Modifiers == ModifierKeys.Control && e.Key == Key.Q)
 {
 if (_hotkeyGate) { e.Handled = true; return true; }
 _hotkeyGate = true;
 try { CycleLineStyle(); }
 finally
 {
 var cc = activeChartControl;
 if (cc != null)
 cc.Dispatcher.BeginInvoke(new Action(() => _hotkeyGate = false),
 System.Windows.Threading.DispatcherPriority.Background);
 else _hotkeyGate = false;
 }
 e.Handled = true;
 return true;
 }
 
 // + (OemPlus/Add) increases width
 if ((e.Key == Key.OemPlus || e.Key == Key.Add) &&
 (Keyboard.Modifiers == ModifierKeys.None || Keyboard.Modifiers == ModifierKeys.Shift))
 {
 if (_hotkeyGate) { e.Handled = true; return true; }
 _hotkeyGate = true;
 try { AdjustLineWidth(+StepWidth); }
 finally
 {
 var cc = activeChartControl;
 if (cc != null)
 cc.Dispatcher.BeginInvoke(new Action(() => _hotkeyGate = false),
 System.Windows.Threading.DispatcherPriority.Background);
 else _hotkeyGate = false;
 }
 e.Handled = true;
 return true;
 }
 
 // − (OemMinus/Subtract) decreases width
 if ((e.Key == Key.OemMinus || e.Key == Key.Subtract) &&
 Keyboard.Modifiers == ModifierKeys.None)
 {
 if (_hotkeyGate) { e.Handled = true; return true; }
 _hotkeyGate = true;
 try { AdjustLineWidth(-StepWidth); }
 finally
 {
 var cc = activeChartControl;
 if (cc != null)
 cc.Dispatcher.BeginInvoke(new Action(() => _hotkeyGate = false),
 System.Windows.Threading.DispatcherPriority.Background);
 else _hotkeyGate = false;
 }
 e.Handled = true;
 return true;
 }
 
 return false;
 }
 
 private ChartBars GetBarsForAnchors(ChartControl cc)
 {
 if (cc == null) return null;
 int panelIdx = ChartPanel != null ? ChartPanel.PanelIndex : anchorPanelIndex;
 return GetBarsForPanel(cc, panelIdx);
 }
 
 private ChartBars GetBarsForAnchorsOld(ChartControl cc)
 {
 if (cc == null) return null;
 
 int slot = -1;
 if (EndAnchor != null && EndAnchor.SlotIndex >= 0) slot = (int)EndAnchor.SlotIndex;
 else if (StartAnchor != null && StartAnchor.SlotIndex >= 0) slot = (int)StartAnchor.SlotIndex;
 
 if (slot >= 0 && slot < cc.BarsArray.Count)
 return cc.BarsArray[slot];
 
 // Fallback: keep your old panel-based lookup if SlotIndex is unknown
 int panelIdx = ChartPanel != null ? ChartPanel.PanelIndex : anchorPanelIndex;
 return GetBarsForPanel(cc, panelIdx);
 }
 
 // Return the first ChartBars that renders in the given panel
 private ChartBars GetBarsForPanel(ChartControl cc, int targetPanelIndex)
 {
 if (cc == null || cc.BarsArray == null) return null;
 for (int i = 0; i < cc.BarsArray.Count; i++)
 {
 var b = cc.BarsArray[i];
 if (b != null && b.ChartPanel.PanelIndex == targetPanelIndex)
 return b;
 }
 return null;
 }
 
 private static DateTime TimeAtBarX(ChartControl cc, ChartBars bars, int barIdx)
 {
 // Get the exact pixel X the LTL uses…
 double xAbs = cc.GetXByBarIndex(bars, barIdx);
 // …and invert it to a chart time so anchors land on the same X.
 return cc.GetTimeByX((int)Math.Round(xAbs));
 }
 
 private ChartBars GetActiveBars(ChartControl cc, ChartScale cs)
 {
 if (cc == null) return null;
 int panelIdx = cs != null ? cs.PanelIndex
 : (ChartPanel != null ? ChartPanel.PanelIndex : anchorPanelIndex);
 return GetBarsForPanel(cc, panelIdx);
 }
 
 private ChartScale ResolveScale(ChartControl cc, ChartPanel cp, ChartScale incoming)
 {
 if (incoming != null) return incoming;
 if (cc == null || cp == null) return null;
 
 try
 {
 var panel = cc.ChartPanels[cp.PanelIndex];
 // Prefer the right-justified scale; fall back to left if needed
 var s = panel?.Scales?[ScaleJustification.Right];
 if (s == null)
 s = panel?.Scales?[ScaleJustification.Left];
 return s;
 }
 catch
 {
 return null;
 }
 }
 
 private static void DeferInvalidate(ChartControl cc)
 {
 if (cc == null) return;
 cc.Dispatcher.BeginInvoke(
 new Action(cc.InvalidateVisual),
 System.Windows.Threading.DispatcherPriority.Render);
 }
 
 // Put this helper in your class
 private static DateTime BarCenterTime(ChartBars bars, ChartControl cc, int idx)
 {
 // Right edge (NT’s bar timestamp is typically the close)
 DateTime right = bars.GetTimeByBarIdx(cc, idx);
 // Left edge = prior bar’s timestamp (fallback: a hair before right)
 DateTime left = idx > 0 ? bars.GetTimeByBarIdx(cc, idx - 1)
 : right.AddMilliseconds(-1);
 long mid = left.Ticks + ((right.Ticks - left.Ticks) / 2);
 return new DateTime(mid, DateTimeKind.Unspecified);
 }
 
 public override Cursor GetCursor(ChartControl chartControl, ChartPanel chartPanel, ChartScale chartScale, Point point)
 {
 // Pre-click path: PanelIndex is -1, so derive bars from the hovered panel.
 if (DrawingState == DrawingState.Building)
 {
 if (chartControl == null) return Cursors.Pen;
 
 ChartPanel cp = chartPanel ?? (chartControl.ChartPanels.Count > 0 ? chartControl.ChartPanels[0] : null);
 if (cp == null) return Cursors.Pen;
 
 ChartScale cs = ResolveScale(chartControl, cp, chartScale);
 if (cs == null) return Cursors.Pen;
 
 var bars = GetBarsForPanel(chartControl, cp.PanelIndex);
 if (bars != null && bars.Count > 0)
 UpdateHoverFromPoint(chartControl, cp, cs, point /* panel coords */, bars);
 
 return Cursors.Pen;
 }
 
 switch (DrawingState)
 {
 case DrawingState.Moving: return IsLocked ? Cursors.No : Cursors.SizeAll;
 case DrawingState.Editing:
 if (IsLocked)
 return Cursors.No;
 
 return editingAnchor == StartAnchor ? Cursors.SizeNESW : Cursors.SizeNWSE;
 default:
 // Draw move cursor if cursor is near line path anywhere
 Point startPoint = StartAnchor.GetPoint(chartControl, chartPanel, chartScale);
 
 ChartAnchor closest = GetClosestAnchor(chartControl, chartPanel, chartScale, cursorSensitivity, point);
 if (closest != null)
 {
 if (IsLocked)
 return Cursors.Arrow;
 return closest == StartAnchor ? Cursors.SizeNESW : Cursors.SizeNWSE;
 }
 
 Point endPoint = EndAnchor.GetPoint(chartControl, chartPanel, chartScale);
 Point minPoint = startPoint;
 Point maxPoint = endPoint;
 
 Vector totalVector = maxPoint - minPoint;
 return MathHelper.IsPointAlongVector(point, minPoint, totalVector, cursorSensitivity) ?
 IsLocked ? Cursors.Arrow : Cursors.SizeAll : null;
 }
 }
 
 public sealed override Point[] GetSelectionPoints(ChartControl chartControl, ChartScale chartScale)
 {
 var panel = chartControl.ChartPanels[chartScale.PanelIndex];
 var lst = new List<Point>(4);
 if (StartAnchor != null) lst.Add(StartAnchor.GetPoint(chartControl, panel, chartScale));
 if (EndAnchor != null) lst.Add(EndAnchor.GetPoint(chartControl, panel, chartScale));
 if (VeStartAnchor != null) lst.Add(VeStartAnchor.GetPoint(chartControl, panel, chartScale));
 if (VeEndAnchor != null) lst.Add(VeEndAnchor.GetPoint(chartControl, panel, chartScale));
 return lst.ToArray();
 }
 
 public override bool IsAlertConditionTrue(AlertConditionItem conditionItem, Condition condition, ChartAlertValue[] values, ChartControl chartControl, ChartScale chartScale)
 {
 if (values.Length < 1)
 return false;
 
 var bars = GetActiveBars(chartControl, chartScale);
 if (bars == null) return false;
 
 var chartPanel = bars.ChartPanel;
 
 // get start / end points of what is absolutely shown for our vector 
 Point lineStartPoint = StartAnchor.GetPoint(chartControl, chartPanel, chartScale);
 Point lineEndPoint = EndAnchor.GetPoint(chartControl, chartPanel, chartScale);
 
 double minLineX = double.MaxValue;
 double maxLineX = double.MinValue; 
 foreach (Point point in new[]{lineStartPoint, lineEndPoint})
 {
 minLineX = Math.Min(minLineX, point.X);
 maxLineX = Math.Max(maxLineX, point.X);
 }
 
 // first thing, if our smallest x is greater than most recent bar, we have nothing to do yet.
 // do not try to check Y because lines could cross through stuff
 double firstBarX = values[0].ValueType == ChartAlertValueType.StaticValue ? minLineX : chartControl.GetXByTime(values[0].Time);
 double firstBarY = chartScale.GetYByValue(values[0].Value);
 
 // dont have to take extension into account as its already handled in min/max line x
 
 // bars completely passed our line
 if (maxLineX < firstBarX)
 return false;
 
 // bars not yet to our line
 if (minLineX > firstBarX)
 return false;
 
 // NOTE: normalize line points so the leftmost is passed first. Otherwise, our vector
 // math could end up having the line normal vector being backwards if user drew it backwards.
 // but we dont care the order of anchors, we want 'up' to mean 'up'!
 Point leftPoint = lineStartPoint.X < lineEndPoint.X ? lineStartPoint : lineEndPoint;
 Point rightPoint = lineEndPoint.X > lineStartPoint.X ? lineEndPoint : lineStartPoint;
 
 Point barPoint = new Point(firstBarX, firstBarY);
 // NOTE: 'left / right' is relative to if line was vertical. it can end up backwards too
 MathHelper.PointLineLocation pointLocation = MathHelper.GetPointLineLocation(leftPoint, rightPoint, barPoint);
 // for vertical things, think of a vertical line rotated 90 degrees to lay flat, where it's normal vector is 'up'
 switch (condition)
 {
 case Condition.Greater: return pointLocation == MathHelper.PointLineLocation.LeftOrAbove;
 case Condition.GreaterEqual: return pointLocation == MathHelper.PointLineLocation.LeftOrAbove || pointLocation == MathHelper.PointLineLocation.DirectlyOnLine;
 case Condition.Less: return pointLocation == MathHelper.PointLineLocation.RightOrBelow;
 case Condition.LessEqual: return pointLocation == MathHelper.PointLineLocation.RightOrBelow || pointLocation == MathHelper.PointLineLocation.DirectlyOnLine;
 case Condition.Equals: return pointLocation == MathHelper.PointLineLocation.DirectlyOnLine;
 case Condition.NotEqual: return pointLocation != MathHelper.PointLineLocation.DirectlyOnLine;
 case Condition.CrossAbove:
 case Condition.CrossBelow:
 Predicate<ChartAlertValue> predicate = v =>
 {
 double barX = chartControl.GetXByTime(v.Time);
 double barY = chartScale.GetYByValue(v.Value);
 Point stepBarPoint = new Point(barX, barY);
 MathHelper.PointLineLocation ptLocation = MathHelper.GetPointLineLocation(leftPoint, rightPoint, stepBarPoint);
 if (condition == Condition.CrossAbove)
 return ptLocation == MathHelper.PointLineLocation.LeftOrAbove;
 return ptLocation == MathHelper.PointLineLocation.RightOrBelow;
 };
 return MathHelper.DidPredicateCross(values, predicate);
 }
 
 return false;
 }
 
 public override bool IsVisibleOnChart(ChartControl chartControl, ChartScale chartScale, DateTime firstTimeOnChart, DateTime lastTimeOnChart)
 {
 if (DrawingState == DrawingState.Building)
 return true;
 
 DateTime minTime = Core.Globals.MaxDate;
 DateTime maxTime = Core.Globals.MinDate;
 
 // check at least one of our anchors is in horizontal time frame
 foreach (ChartAnchor anchor in Anchors)
 {
 if (anchor.Time < minTime)
 minTime = anchor.Time;
 if (anchor.Time > maxTime)
 maxTime = anchor.Time;
 }
 
 // hline extends, but otherwise try to check if line horizontally crosses through visible chart times in some way
 if (minTime > lastTimeOnChart || maxTime < firstTimeOnChart)
 return false;
 
 return true;
 }
 
 public override void OnCalculateMinMax()
 {
 MinValue = double.MaxValue;
 MaxValue = double.MinValue;
 
 if (!IsVisible)
 return;
 
 // return min/max values only if something has been actually drawn
 if (Anchors.Any(a => !a.IsEditing))
 foreach (ChartAnchor anchor in Anchors)
 {
 MinValue = Math.Min(anchor.Price, MinValue);
 MaxValue = Math.Max(anchor.Price, MaxValue);
 }
 }
 
 
 /// <summary>
 /// Computes a “hover hit” on bar highs/lows near the mouse, in the **panel’s coordinate space**.
 /// </summary>
 private void UpdateHoverFromPoint(ChartControl cc, ChartPanel panel, ChartScale scale, Point mousePtPanel, ChartBars bars)
 {
 var prevHover = hoverHitPx;
 hoverHitPx = null;
 
 if (bars == null || bars.Count == 0) return;
 
 int mouseAbsX = (int)(mousePtPanel.X + panel.X);
 int idx = bars.GetBarIdxByX(cc, mouseAbsX);
 if (idx < 0 || idx >= bars.Count) return;
 
 double hi = bars.Bars.GetHigh(idx);
 double lo = bars.Bars.GetLow(idx);
 double x = cc.GetXByBarIndex(bars, idx); // absolute X for this bar
 double hiY = scale.GetYByValue(hi);
 double loY = scale.GetYByValue(lo);
 
 double tolX = Math.Max(6, cc.BarWidth + 2);
 
 if (Math.Abs(mouseAbsX - x) <= tolX && Math.Abs(mousePtPanel.Y - hiY) <= hoverTolPx)
 hoverHitPx = new Point(x, hiY);
 else if (Math.Abs(mouseAbsX - x) <= tolX && Math.Abs(mousePtPanel.Y - loY) <= hoverTolPx)
 hoverHitPx = new Point(x, loY);
 
 if ((prevHover == null) != (hoverHitPx == null) ||
 (prevHover != null && hoverHitPx != null &&
 (Math.Abs(prevHover.Value.X - hoverHitPx.Value.X) > double.Epsilon ||
 Math.Abs(prevHover.Value.Y - hoverHitPx.Value.Y) > double.Epsilon)))
 {
 //DeferInvalidate(cc);
	 RequestRepaint(cc);
 }
 }
 
 private ChartAnchor SnapToHiLo(
 ChartControl chartControl,
 ChartPanel chartPanel,
 ChartScale chartScale,
 int mouseAbsX, // absolute X (chart-control coords)
 double mousePanelY) // panel-relative Y
 {
 _snapRectDx = null;
 
 var bars =GetActiveBars(chartControl, chartScale);
 if (bars == null || bars.Count <= 0)
 return null;
 
 int idx = bars.GetBarIdxByX(chartControl, mouseAbsX); // <-- absolute X now
 if (idx < 0 || idx >= bars.Count)
 return null;
 
 int lo = Math.Max(0, idx - _snapLookaround);
 int hi = Math.Min(bars.Count - 1, idx + _snapLookaround);
 double tolX = Math.Max(6, chartControl.BarWidth + 2);
 
 for (int i = lo; i <= hi; i++)
 {
 double bh = bars.Bars.GetHigh(i);
 double bl = bars.Bars.GetLow(i);
 
 double barAbsX = chartControl.GetXByBarIndex(bars, i); // absolute X
 double hiY = chartScale.GetYByValue(bh); // panel-relative Y
 double loY = chartScale.GetYByValue(bl);
 
 if (Math.Abs(mouseAbsX - barAbsX) <= tolX && Math.Abs(mousePanelY - hiY) <= _snapYTolPx)
 {
 _snapRectDx = new SharpDX.RectangleF((float)(barAbsX - _snapSizePx/2f),
 (float)(hiY - _snapSizePx/2f),
 _snapSizePx, _snapSizePx);
 
 var a = new ChartAnchor { DrawingTool = this };
 a.Time = bars.GetTimeByBarIdx(chartControl, i);
 a.Price = bh;
 return a;
 }
 
 if (Math.Abs(mouseAbsX - barAbsX) <= tolX && Math.Abs(mousePanelY - loY) <= _snapYTolPx)
 {
 _snapRectDx = new SharpDX.RectangleF((float)(barAbsX - _snapSizePx/2f),
 (float)(loY - _snapSizePx/2f),
 _snapSizePx, _snapSizePx);
 
 var a = new ChartAnchor { DrawingTool = this };
 a.Time = bars.GetTimeByBarIdx(chartControl, i);
 a.Price = bl;
 return a;
 }
 }
 return null;
 }
 
 private void DrawNumberLabel(
 ChartControl cc,
 ChartScale cs,
 ChartBars bars,
 int barIndex,
 bool placeAbove, // true = above high, false = below low
 string text,
 float yOffsetPx,
 double? xOverrideAbs = null) // pass StartAnchor X here for #1; else null
 {
 if (RenderTarget == null || bars == null || barIndex < 0 || barIndex >= bars.Count)
 return;
 
 double xAbs = xOverrideAbs ?? cc.GetXByBarIndex(bars, barIndex);
 
 var series = bars.Bars;
 double baseY = placeAbove
 ? cs.GetYByValue(series.GetHigh(barIndex))
 : cs.GetYByValue(series.GetLow(barIndex));
 
 using (var tf = cc.Properties.LabelFont.ToDirectWriteTextFormat())
 {
 using (var layout = new SharpDX.DirectWrite.TextLayout(
 NinjaTrader.Core.Globals.DirectWriteFactory, text, tf, 64f, 32f))
 {
 var m = layout.Metrics;
 float w = Math.Max(1f, m.WidthIncludingTrailingWhitespace);
 float h = Math.Max(1f, m.Height);
 
 float left = (float)(xAbs - 0.5 * w);
 float top = placeAbove
 ? (float)(baseY - (yOffsetPx + h))
 : (float)(baseY + yOffsetPx);
 
 var rect = new SharpDX.RectangleF(left, top, w, h);
 RenderTarget.DrawText(text, tf, rect, LineStroke.BrushDX);
 }
 }
 }
 
 private void EnsureAutoTimer()
 {
 if (_autoTimer != null) return;
 
 _autoTimer = new System.Windows.Threading.DispatcherTimer(
 System.Windows.Threading.DispatcherPriority.Background);
 _autoTimer.Interval = TimeSpan.FromMilliseconds(Math.Max(50, AutoExtendIntervalMs));
 _autoTimer.Tick += AutoTimer_Tick;
 }
 
 private void StartAutoExtend()
 {
 EnsureAutoTimer();
 if (_autoRunning) return;
 
 _autoTimer.Start();
 _autoRunning = true;
 PrintDebug("Auto-extend: started");
 }
 
 private void StopAutoExtend()
 {
 if (_autoTimer == null) return;
 if (!_autoRunning) return;
 
 _autoTimer.Stop();
 _autoRunning = false;
 PrintDebug("Auto-extend: stopped");
 }
 
 private bool IsBreakAtIndex(ChartBars bars, int idx, double slope, int sIdx, double sPrice, bool isUp)
 {
 if (bars == null || idx < 0 || idx >= bars.Count) return false;
 var series = bars.Bars;
 
 double yLine = sPrice + slope * (idx - sIdx);
 
 if (ExtendBreakRule == BreakMode.HighLowPenetration)
 {
 double hi = series.GetHigh(idx);
 double lo = series.GetLow(idx);
 return isUp ? (lo < yLine) : (hi > yLine);
 }
 else // CloseCross
 {
 double c = series.GetClose(idx);
 return isUp ? (c < yLine) : (c > yLine);
 }
 }
 
 // Map time -> index, but floor to the bar at/BEFORE 't'.
 private int IndexAtOrBefore(ChartBars bars, ChartControl cc, DateTime t)
 {
 int idx = bars.GetBarIdxByTime(cc, t);
 if (idx < 0) return bars.Count - 1;
 DateTime idxTime = bars.GetTimeByBarIdx(cc, idx);
 if (idxTime > t && idx > 0) idx--; // floor if rounded up
 return idx;
 }
 
 private void AutoTimer_Tick(object sender, EventArgs e)
 {
 if (!AutoExtend || _isExtending || IsLocked || DrawingState != DrawingState.Normal) return;
 
 var cc = activeChartControl ?? ChartPanel?.ChartControl;
 if (cc == null) return;
 
 var cp = (anchorPanelIndex >= 0 && cc.ChartPanels.Count > anchorPanelIndex)
 ? cc.ChartPanels[anchorPanelIndex]
 : ChartPanel;
 if (cp == null) return;
 
 var cs = ResolveScale(cc, cp, null);
 if (cs == null) return;
 
 var bars = GetBarsForAnchors(cc);
 if (bars == null || bars.Count == 0) return;
 
 int sIdx = _lastSIdx ?? IndexAtOrBefore(bars, cc, StartAnchor.Time);
 int eIdx = _lastEIdx ?? IndexAtOrBefore(bars, cc, EndAnchor.Time);
 
 if (sIdx < 0 || eIdx < 0 || sIdx == eIdx) return;
 
 bool isUp = EndAnchor.Price >= StartAnchor.Price;
 double slope = (_lastSIdx.HasValue && _lastEIdx.HasValue && _lastEIdx.Value != _lastSIdx.Value)
 ? _lastSlope
 : (EndAnchor.Price - StartAnchor.Price) / Math.Max(1, (eIdx - sIdx));
 
 int lastIdx = bars.Count - 1;
 int nextIdx = eIdx + 1;
 
 if (nextIdx > lastIdx) return;
 
 if (IsBreakAtIndex(bars, nextIdx, slope, sIdx, StartAnchor.Price, isUp))
 {
 StopAutoExtend();
 return;
 }
 
 _keepP2ThisPass = _lastP2Idx.HasValue; // keep P2 while auto-extending
 ExtendRTL(cc, cs);
 _keepP2ThisPass = false;
 }
 
 public override void OnMouseDown(ChartControl chartControl, ChartPanel chartPanel, ChartScale chartScale, ChartAnchor dataPoint)
 {
	 switch (DrawingState)
	 {
		 case DrawingState.Building:
			 if (StartAnchor.IsEditing)
			 {
				 dataPoint.CopyDataValues(StartAnchor);
				 StartAnchor.IsEditing = false;
				 
				 dataPoint.CopyDataValues(EndAnchor);
			 }
			 else if (EndAnchor.IsEditing)
			 {
				 dataPoint.CopyDataValues(EndAnchor);
				 EndAnchor.IsEditing = false;
			 }
			 
			 if (!StartAnchor.IsEditing && !EndAnchor.IsEditing)
			 {
				 DrawingState = DrawingState.Normal;

			    var cc   = chartControl;
			    var cb   = GetBarsForAnchors(cc);   // <-- ChartBars
			    if (cc != null && cb != null)
			        FreezeStartAnchor(StartAnchor, cc, cb);
			
			    CalculateLTLCoordinates(chartControl, chartScale);
			    IsSelected = false;
			 }
		 break;
		 case DrawingState.Normal:
		 Point point = dataPoint.GetPoint(chartControl, chartPanel, chartScale);
		 editingAnchor = GetClosestAnchor(chartControl, chartPanel, chartScale, cursorSensitivity, point);
		 anchorPanelIndex = chartPanel.PanelIndex;
		 
		 if (editingAnchor != null)
		 {
		 editingAnchor.IsEditing = true;
		 DrawingState = DrawingState.Editing;
		 
		 // keep P2 while user adjusts the RTL end
		 _keepP2ThisPass = ( (editingAnchor == EndAnchor || editingAnchor == VeEndAnchor) && _lastP2Idx.HasValue );
		 
		 if (AutoExtend) StopAutoExtend();
		 
		 CalculateLTLCoordinates(chartControl, chartScale);
		 }
		 else
		 {
		 if (GetCursor(chartControl, chartPanel, chartScale, point) != null)
		 {
		 DrawingState = DrawingState.Moving;
		 }
		 else
		 IsSelected = false;
		 }
		 break;
	 }
 
 }
 
 public override void OnMouseMove(ChartControl chartControl, ChartPanel chartPanel, ChartScale chartScale, ChartAnchor dataPoint)
 {
 var prevHover = hoverHitPx;
 hoverHitPx = null;
 
 var bars = GetBarsForAnchors(chartControl);
 if (bars != null)
 {
 var mousePt = dataPoint.GetPoint(chartControl, chartPanel, chartScale);
 int idx = bars.GetBarIdxByTime(chartControl, dataPoint.Time);
 if (idx >= 0 && idx < bars.Count)
 {
 double hi = bars.Bars.GetHigh(idx);
 double lo = bars.Bars.GetLow(idx);
 
 double barX = chartControl.GetXByBarIndex(bars, idx);
 double hiY = chartScale.GetYByValue(hi);
 double loY = chartScale.GetYByValue(lo);
 
 if (Math.Abs(mousePt.Y - hiY) <= hoverTolPx && Math.Abs(mousePt.X - barX) <= chartControl.BarWidth + 2)
 hoverHitPx = new Point(barX, hiY);
 else if (Math.Abs(mousePt.Y - loY) <= hoverTolPx && Math.Abs(mousePt.X - barX) <= chartControl.BarWidth + 2)
 hoverHitPx = new Point(barX, loY);
 }
 }
 
 if (IsLocked && DrawingState != DrawingState.Building)
 return;
 
 Point mousePxPanel = Mouse.GetPosition(chartPanel);
 int mouseAbsX = (int)(mousePxPanel.X + chartPanel.X);
 
 var prevRect = _snapRectDx;
 
 if (DrawingState == DrawingState.Editing && editingAnchor == VeEndAnchor)
 {
 SnapToHiLo(chartControl, chartPanel, chartScale, mouseAbsX, mousePxPanel.Y);
 }
 else
 {
 _snapRectDx = null;
 }
 
 if (DrawingState == DrawingState.Building)
 {
 if (EndAnchor.IsEditing)
 {
 dataPoint.CopyDataValues(EndAnchor);
 CalculateLTLCoordinates(chartControl, chartScale);
 }
 }
 else if (DrawingState == DrawingState.Editing && editingAnchor != null)
 {
 bool recalced = false;
 dataPoint.CopyDataValues(editingAnchor);
 
 var barsLocal = GetBarsForAnchors(chartControl);
 
 if (editingAnchor == VeEndAnchor)
 {
 // VE drag extends the RTL **without changing slope** (container doesn’t pivot).
 if (barsLocal != null)
 {
 //int veEndIndex = barsLocal.GetBarIdxByTime(chartControl, VeEndAnchor.Time);
 int veEndIndex = IndexAtOrBefore(barsLocal, chartControl, VeEndAnchor.Time);
 if (veEndIndex >= 0 && veEndIndex < barsLocal.Count)
 {
 // Lock slope: y = y0 m * (x - x0), using the stamped RTL end (rtlEndPointX/Price)
 DateTime veEndTime = barsLocal.GetTimeByBarIdx(chartControl, veEndIndex);
 double projectedY = rtlEndPointPrice + lineSlope * (veEndIndex - rtlEndPointX);
 
 // Extend RTL in time, keep price on the locked slope
 EndAnchor.Time = veEndTime;
 EndAnchor.Price = projectedY;
 
 // Keep caches in sync so subsequent ticks are stable
 _lastEIdx = veEndIndex;
 rtlEndPointX = veEndIndex;
 rtlEndPointPrice = EndAnchor.Price;
 
 // Mirror VE to the projected tip so you see the LTL projection during drag
 VeEndAnchor.Time = veEndTime;
 VeEndAnchor.Price = projectedY;
 
 EndAnchor.SlotIndex = veEndIndex; // NEW
 VeEndAnchor.SlotIndex = veEndIndex; // NEW
 
 try
 {
 CalculateLTLCoordinates(chartControl, chartScale);
 recalced = true;
 }
 catch (Exception ex)
 {
 PrintDebug("OnMouseMove (VeEnd): " + ex);
 }
 }
 }
 }
 else if (editingAnchor == EndAnchor)
 {
 // Dragging the actual RTL end
 if (barsLocal != null)
 {
 int eIdx = IndexAtOrBefore(barsLocal, chartControl, EndAnchor.Time);
 //EndAnchor.SlotIndex = eIdx;
 _lastEIdx = eIdx;
 rtlEndPointX = eIdx;
 rtlEndPointPrice = EndAnchor.Price;
 
 EndAnchor.SlotIndex = eIdx; // NEW
 }
 
 try
 {
 CalculateLTLCoordinates(chartControl, chartScale);
 recalced = true;
 }
 catch (Exception ex)
 {
 PrintDebug("OnMouseMove (End): " + ex);
 }
 }
 
 // If we recalculated geometry, trigger a repaint immediately
 if (recalced)
 {
 //DeferInvalidate(chartControl);
	 RequestRepaint(chartControl);
 return; // we already invalidated; no need to rely on hover/snap invalidation below
 }
 }
 else if (DrawingState == DrawingState.Moving)
 {
 foreach (ChartAnchor anchor in Anchors)
 anchor.MoveAnchor(InitialMouseDownAnchor, dataPoint, chartControl, chartPanel, chartScale, this);
 }
 
 if (prevHover != hoverHitPx || 
 prevRect.HasValue != _snapRectDx.HasValue ||
 (prevRect.HasValue && _snapRectDx.HasValue &&
 (prevRect.Value.X != _snapRectDx.Value.X || prevRect.Value.Y != _snapRectDx.Value.Y)))
 {
 //chartControl.InvalidateVisual();
	 RequestRepaint(chartControl);
 }
 }
 
 public override void OnMouseUp(ChartControl chartControl, ChartPanel chartPanel, ChartScale chartScale, ChartAnchor dataPoint) 
 {
   if (DrawingState == DrawingState.Moving || DrawingState == DrawingState.Editing)
     DrawingState = DrawingState.Normal;
   if (editingAnchor != null) 
   {
     editingAnchor.IsEditing = false;
     if (editingAnchor == VeEndAnchor || editingAnchor == EndAnchor) {
       try 
	   {
         CalculateLTLCoordinates(chartControl, chartScale);
       } 
	   catch (System.Exception e) 
	   {
         Print("OnMouseUp : " + e.ToString());
       } 
	   finally 
	   {
         //_lockP2DuringRtlDrag = false; // release the lock after the adjustment is finalized
         //_p2FrozenIdx = null; // end of drag = unfreeze
         _keepP2ThisPass = false; // <- reset the scoped flag
         //_lockP2DuringRtlDrag = false;
       }
     }
   }
   editingAnchor = null;

   rtlEndPointPrice = EndAnchor.Price;

   var bars = GetBarsForAnchors(chartControl);
   if (bars == null)
     return;

   rtlEndPointX = IndexAtOrBefore(bars, chartControl, EndAnchor.Time);
   _lastEIdx = rtlEndPointX;

   EndAnchor.SlotIndex = rtlEndPointX; // NEW
   VeEndAnchor.SlotIndex = rtlEndPointX; // NEW (keeps the handle visually on the same bar)

   
   
   if (AutoExtend) StartAutoExtend();
   
   PublishManualSnapshotIfReady(chartControl, bars);
 }
 
 public override void OnEdited(ChartControl chartControl, ChartPanel chartPanel, ChartScale chartScale, DrawingTool oldinstance)
 {
 base.OnEdited(chartControl, chartPanel, chartScale, oldinstance);
 
 if (chartControl == null || chartScale == null)
 return;
 
 CalculateLTLCoordinates(chartControl, chartScale);
 }
 
 public override void OnRender(ChartControl chartControl, ChartScale chartScale)
 {
 if (_isExtending) return;
 
 _lastChartScale = chartScale;
 
 if (chartControl == null || chartScale == null || RenderTarget == null) return;
 if (LineStroke == null || StartAnchor == null || EndAnchor == null) return;
 
 if (activeChartControl == null)
 SetContextMenuHandlers(chartControl,chartScale);
 
 EnsureAutoTimer();
 
 if (AutoExtend && !_autoRunning) StartAutoExtend();
 if (!AutoExtend && _autoRunning) StopAutoExtend();
 
 if (_autoTimer != null)
 {
 var desired = TimeSpan.FromMilliseconds(Math.Max(50, AutoExtendIntervalMs));
 if (_autoTimer.Interval != desired)
 _autoTimer.Interval = desired;
 }
 
 if (segments.Count == 0 &&
 !_recalcAfterReloadTried &&
 !StartAnchor.IsEditing && !EndAnchor.IsEditing)
 {
 _recalcAfterReloadTried = true;
 try { CalculateLTLCoordinates(chartControl, chartScale); }
 catch (Exception ex) { Print("OnRender lazy recalc: " + ex.Message); }
 }
 
 try {
 LineStroke.RenderTarget = RenderTarget;
 RenderTarget.AntialiasMode = SharpDX.Direct2D1.AntialiasMode.PerPrimitive;
 
 var panel = chartControl.ChartPanels[chartScale.PanelIndex];
 
 if (UpBrush == null) UpBrush = Brushes.Blue;
 if (DownBrush == null) DownBrush = Brushes.Red;
 LineStroke.Brush = isUpContainer ? UpBrush : DownBrush;
 
 if ((DrawingState == DrawingState.Building || DrawingState == DrawingState.Normal) && hoverHitPx.HasValue)
 {
 using (var blueBrush = new SharpDX.Direct2D1.SolidColorBrush(RenderTarget, new SharpDX.Color(0, 120, 215, 180)))
 {
 var rect = new SharpDX.RectangleF(
 (float)(hoverHitPx.Value.X - _snapSizePx / 2f),
 (float)(hoverHitPx.Value.Y - _snapSizePx / 2f),
 _snapSizePx,
 _snapSizePx
 );
 RenderTarget.FillRectangle(rect, blueBrush);
 
 using (var borderBrush = new SharpDX.Direct2D1.SolidColorBrush(RenderTarget, new SharpDX.Color(0, 80, 180, 255)))
 {
 RenderTarget.DrawRectangle(rect, borderBrush, 1f);
 }
 }
 }
 
 if (!IsInHitTest && DrawingState == DrawingState.Editing && _snapRectDx.HasValue)
 {
 using (var snapBrush = new SharpDX.Direct2D1.SolidColorBrush(RenderTarget, new SharpDX.Color(255, 165, 0, 180)))
 {
 RenderTarget.FillRectangle(_snapRectDx.Value, snapBrush);
 }
 }
 
 double strokePixAdj = ((double)(LineStroke.Width % 2)).ApproxCompare(0) == 0 ? 0.5 : 0.0;
 Vector pixelAdjustVec = new Vector(strokePixAdj, strokePixAdj);
 
 // RTL
 Point startPoint = StartAnchor.GetPoint(chartControl, panel, chartScale);
 Point endPoint = EndAnchor.GetPoint(chartControl, panel, chartScale);
 
 var brushDX = IsInHitTest && chartControl.SelectionBrush != null
 ? chartControl.SelectionBrush
 : LineStroke.BrushDX;
 
 RenderTarget.DrawLine((startPoint + pixelAdjustVec).ToVector2(),
 (endPoint + pixelAdjustVec).ToVector2(),
 brushDX, LineStroke.Width, LineStroke.StrokeStyle);
 
 
 var bars = GetBarsForAnchors(chartControl);
 if (bars == null) return;
 
 foreach (var seg in segments)
 {
 int sIdx = seg.SIdx, eIdx = seg.EIdx;
 double sPrice = seg.SY, ePrice = seg.EY;
 if (sIdx < 0 || eIdx < 0 || sIdx >= bars.Count || eIdx >= bars.Count) continue;
 
 Point segStart = new Point(chartControl.GetXByBarIndex(bars, sIdx), chartScale.GetYByValue(sPrice));
 Point segEnd = new Point(chartControl.GetXByBarIndex(bars, eIdx), chartScale.GetYByValue(ePrice));
 
 RenderTarget.DrawLine((segStart + pixelAdjustVec).ToVector2(),
 (segEnd + pixelAdjustVec).ToVector2(),
 brushDX, LineStroke.Width, LineStroke.StrokeStyle);
 }
 
 if (_showNumbers && _lastSIdx.HasValue && _lastP2Idx.HasValue && _lastP3Idx.HasValue)
 {
 var barsNum = GetActiveBars(chartControl, chartScale);
 if (barsNum != null && barsNum.Count > 0)
 {
 panel = chartControl.ChartPanels[chartScale.PanelIndex];
 
 int p1Idx = _lastSIdx.Value;
 int p2Idx = _lastP2Idx.Value;
 int p3Idx = _lastP3Idx.Value;
 
 double p1AbsX = StartAnchor.GetPoint(chartControl, panel, chartScale).X;
 
 const float belowNudge = 3f;
 const float aboveNudge = 4f;
 
 if (isUpContainer)
 {
 DrawNumberLabel(chartControl, chartScale, barsNum, p1Idx, /*above*/ false, "1", belowNudge, p1AbsX);
 DrawNumberLabel(chartControl, chartScale, barsNum, p2Idx, /*above*/ true, "2", aboveNudge);
 DrawNumberLabel(chartControl, chartScale, barsNum, p3Idx, /*above*/ false, "3", belowNudge);
 }
 else
 {
 DrawNumberLabel(chartControl, chartScale, barsNum, p1Idx, /*above*/ true, "1", aboveNudge, p1AbsX);
 DrawNumberLabel(chartControl, chartScale, barsNum, p2Idx, /*above*/ false, "2", belowNudge);
 DrawNumberLabel(chartControl, chartScale, barsNum, p3Idx, /*above*/ true, "3", aboveNudge);
 }
 }
 }
 
 }
 catch(System.Exception e) {
 Print("System exception : " + e.ToString());
 }
 }
 
 private void UpdateVeAnchorsFromLastSegment(ChartControl chartControl)
 {
 var bars = GetBarsForAnchors(chartControl);
 if (bars == null || segments.Count == 0) return;
 
 var last = segments[segments.Count - 1];
 int sIdx = last.SIdx;
 double sY = last.SY;
 
 int eIdx =
 (rtlEndPointX >= 0 && rtlEndPointX < bars.Count) ? rtlEndPointX :
 (_lastEIdx.HasValue && _lastEIdx.Value >= 0 && _lastEIdx.Value < bars.Count) ? _lastEIdx.Value :
 IndexAtOrBefore(bars, chartControl, EndAnchor.Time);
 
 if (sIdx < 0 || eIdx < 0 || sIdx >= bars.Count || eIdx >= bars.Count) return;
 if (eIdx < sIdx) eIdx = sIdx;
 
 double eY = sY + lineSlope * (eIdx - sIdx);
 
 // *** key change: stamp Times from the exact bar X we draw with ***
 VeStartAnchor.Time = bars.GetTimeByBarIdx(chartControl, sIdx);
 VeStartAnchor.Price = sY;
 VeStartAnchor.SlotIndex = sIdx;
 
 VeEndAnchor.Time   = bars.GetTimeByBarIdx(chartControl, eIdx);
 VeEndAnchor.Price = eY;
 VeEndAnchor.SlotIndex = eIdx;
 
 VeStartAnchor.IsBrowsable = true;
 VeEndAnchor.IsBrowsable = true;
 
 PrintDebug($"[VE] sIdx={sIdx} eIdx={eIdx}");
 
 // Sanity: verify pixel-perfect alignment (should be 0)
 double segX = chartControl.GetXByBarIndex(bars, sIdx);
 double veSX = chartControl.GetXByTime(VeStartAnchor.Time);
 PrintDebug($"VE start px delta = {segX - veSX:0.###}");
 }
 
 
 
 
 private void UpdateVeAnchorsFromLastSegmentEx(ChartControl chartControl)
 {
 var bars = GetBarsForAnchors(chartControl);
 if (bars == null || segments.Count == 0) return;
 
 var last = segments[segments.Count - 1];
 int sIdx = last.SIdx;
 double sY = last.SY;
 
 // Prefer the stamped/cached RTL end index; fall back to time only if needed.
 int eIdx =
 (rtlEndPointX >= 0 && rtlEndPointX < bars.Count) ? rtlEndPointX :
 (_lastEIdx.HasValue && _lastEIdx.Value >= 0 && _lastEIdx.Value < bars.Count) ? _lastEIdx.Value :
 IndexAtOrBefore(bars, chartControl, EndAnchor.Time);
 
 if (sIdx < 0 || eIdx < 0 || sIdx >= bars.Count || eIdx >= bars.Count) return;
 
 double eY = sY + lineSlope * (eIdx - sIdx);
 
 VeStartAnchor.Time = bars.GetTimeByBarIdx(chartControl, sIdx);
 VeStartAnchor.Price = sY;
 VeStartAnchor.SlotIndex = sIdx; // <-- pin to bar
 
 VeEndAnchor.Time = bars.GetTimeByBarIdx(chartControl, eIdx);
 VeEndAnchor.Price = eY;
 VeEndAnchor.SlotIndex = eIdx; // <-- pin to bar
 
 VeStartAnchor.IsBrowsable = true;
 VeEndAnchor.IsBrowsable = true;
 
 PrintDebug($"[VE] sIdx={sIdx} eIdx={eIdx}");
 }
 
 
 
 private void UpdateVeAnchorsFromLastSegmentOldEx(ChartControl chartControl)
 {
 var bars = GetBarsForAnchors(chartControl);
 if (bars == null || segments.Count == 0) return;
 
 // last LTL segment
 var last = segments[segments.Count - 1];
 int sIdxSeg = last.SIdx;
 double sYSeg = last.SY;
 
 // IMPORTANT: use the eIdx we just computed for the container, not a fresh lookup
 int eIdxRtl = _lastEIdx ?? IndexAtOrBefore(bars, chartControl, EndAnchor.Time);
 if (sIdxSeg < 0 || eIdxRtl < 0 || sIdxSeg >= bars.Count || eIdxRtl >= bars.Count) return;
 
 double eY = sYSeg + lineSlope * (eIdxRtl - sIdxSeg);
 
 VeStartAnchor.Time = bars.GetTimeByBarIdx(chartControl, sIdxSeg);
 VeStartAnchor.Price = sYSeg;
 VeStartAnchor.SlotIndex = sIdxSeg;
 
 VeEndAnchor.Time = bars.GetTimeByBarIdx(chartControl, eIdxRtl);
 VeEndAnchor.Price = eY;
 VeEndAnchor.SlotIndex = eIdxRtl;
 
 VeStartAnchor.IsBrowsable = true;
 VeEndAnchor.IsBrowsable = true;
 
 PrintDebug($"[VE] sIdx={sIdxSeg} eIdx={eIdxRtl}");
 }
 
 private void UpdateVeAnchorsFromLastSegmentOLd(ChartControl chartControl)
 {
 var bars = GetBarsForAnchors(chartControl);
 if (bars == null || segments.Count == 0) return;
 
 // Last built LTL segment (start of the last segment)
 var last = segments[segments.Count - 1];
 int sIdxSeg = last.SIdx;
 double sYSeg = last.SY;
 
 // Use the stamped/cached RTL end index; fall back to time only if needed
 //int eIdxRtl = (_lastEIdx.HasValue ? _lastEIdx.Value
 // : IndexAtOrBefore(bars, chartControl, EndAnchor.Time));
 
 int eIdxRtl = IndexAtOrBefore(bars, chartControl, EndAnchor.Time);
 
 if (sIdxSeg < 0 || eIdxRtl < 0 || sIdxSeg >= bars.Count || eIdxRtl >= bars.Count) return;
 
 // Y on the LTL at the RTL end bar (extend the last LTL segment if needed)
 double eY = sYSeg + lineSlope * (eIdxRtl - sIdxSeg);
 
 // Stamp times and slots so NT won’t round us back
 VeStartAnchor.Time = bars.GetTimeByBarIdx(chartControl, sIdxSeg);
 VeStartAnchor.Price = sYSeg;
 //VeStartAnchor.SlotIndex = sIdxSeg;
 
 VeEndAnchor.Time = bars.GetTimeByBarIdx(chartControl, eIdxRtl);
 VeEndAnchor.Price = eY;
 //VeEndAnchor.SlotIndex = eIdxRtl;
 
 VeStartAnchor.IsBrowsable = true;
 VeEndAnchor.IsBrowsable = true;
 }
 
 private void ExtendRTL(ChartControl chartControl, ChartScale chartScale)
 {
		 if (_isExtending) return;
		 
		 var bars = GetBarsForAnchors(chartControl);
		 if (bars == null || bars.Count < 2) return;
		 
		 // Where the RTL end is right now (prefer caches, else floor by time)
		 int currIdx =
		 (rtlEndPointX >= 0 && rtlEndPointX < bars.Count) ? rtlEndPointX :
		 (_lastEIdx.HasValue && _lastEIdx.Value >= 0 && _lastEIdx.Value < bars.Count) ? _lastEIdx.Value :
		 IndexAtOrBefore(bars, chartControl, EndAnchor.Time);
		 
		 int lastIdx = bars.Count - 1;
		 
		 // P1 index (floor), used for slope and y-projection
		 int sIdx = _lastSIdx ?? IndexAtOrBefore(bars, chartControl, StartAnchor.Time);
		 if (sIdx < 0) sIdx = 0;
		 
		 // Keep using the cached slope when available (prevents veer)
		 double slope = (_lastSIdx.HasValue && _lastEIdx.HasValue && _lastEIdx.Value != _lastSIdx.Value)
		 ? _lastSlope
		 : (EndAnchor.Price - StartAnchor.Price) / Math.Max(1, (currIdx - sIdx));
		 
		 int newIdx = currIdx + 1;
		 
		 // ===== CASE 1: already at / beyond the last bar → snap cleanly to last bar =====
		 if (currIdx >= lastIdx)
		 {
			 DateTime lastTm = bars.GetTimeByBarIdx(chartControl, lastIdx);
			 double price = StartAnchor.Price + slope * (lastIdx - sIdx);
			 
			 try
			 {
				 _isExtending = true;
				 
				 EndAnchor.Time = lastTm;
				 EndAnchor.Price = price;
				 
				 EndAnchor.SlotIndex = (currIdx >= lastIdx) ? lastIdx : newIdx; // NEW
				 StartAnchor.SlotIndex = sIdx; // NEW
				 
				 rtlEndPointX = lastIdx;
				 rtlEndPointPrice = price;
				 _lastEIdx = lastIdx;
				 lineSlope = slope;
			 }
			 finally { _isExtending = false; }
			 
			 PrintDebug($"Snapped RTL to last bar {lastIdx} @ {EndAnchor.Price}");
			 CalculateLTLCoordinates(chartControl, chartScale);
			 //DeferInvalidate(chartControl);
			 RequestRepaint(chartControl);
			 
			 return;
 		}
 
		 // ===== CASE 2: normal extend by one bar =====
		 
		 DateTime tm = bars.GetTimeByBarIdx(chartControl, newIdx);
		 double priceN = StartAnchor.Price + slope * (newIdx - sIdx);
		 
		 try
		 {
		 _isExtending = true;
		 
		 EndAnchor.Time = tm;
		 EndAnchor.Price = priceN;
		 
		 EndAnchor.SlotIndex = (currIdx >= lastIdx) ? lastIdx : newIdx; // NEW
		 StartAnchor.SlotIndex = sIdx; // NEW
		 
		 rtlEndPointX = newIdx;
		 rtlEndPointPrice = priceN;
		 _lastEIdx = newIdx;
		 lineSlope = slope;
		 }
		 finally { _isExtending = false; }
		 
		 PrintDebug($"Extend from {currIdx} → {newIdx} @ {EndAnchor.Price}");
		 CalculateLTLCoordinates(chartControl, chartScale);
		 //DeferInvalidate(chartControl);
		 RequestRepaint(chartControl);
		 
		 if (_lastChartScale == null)
    		return;
		 
		 var barsNow = GetActiveBars(chartControl, _lastChartScale);
		 if (barsNow != null)
			  PublishManualSnapshotIfReady(chartControl, barsNow);
 }
 
 private void ExtendRTLOld(ChartControl chartControl, ChartScale chartScale)
 {
 if (_isExtending) return;
 
 var bars = GetBarsForAnchors(chartControl);
 if (bars == null || bars.Count < 2) return;
 
 // Prefer cached indices, then time->index
 int currIdx = (rtlEndPointX >= 0 && rtlEndPointX < bars.Count) ? rtlEndPointX :
 (_lastEIdx.HasValue && _lastEIdx.Value >= 0 && _lastEIdx.Value < bars.Count) ? _lastEIdx.Value :
 IndexAtOrBefore(bars, chartControl, EndAnchor.Time);
 
 if (currIdx >= bars.Count - 1) { PrintDebug("End of bars - container not extended : " + currIdx); return; }
 
 int newIdx = currIdx + 1;
 DateTime tm = bars.GetTimeByBarIdx(chartControl, newIdx);
 
 int sIdx = _lastSIdx ?? IndexAtOrBefore(bars, chartControl, StartAnchor.Time);
 if (sIdx < 0) sIdx = 0;
 
 double slope = (_lastSIdx.HasValue && _lastEIdx.HasValue && _lastEIdx.Value != _lastSIdx.Value)
 ? _lastSlope
 : (EndAnchor.Price - StartAnchor.Price) / Math.Max(1, (currIdx - sIdx));
 
 double price = StartAnchor.Price + slope * (newIdx - sIdx);
 
 try
 {
 _isExtending = true;
 
 EndAnchor.Time = tm;
 EndAnchor.Price = price;
 
 //EndAnchor.SlotIndex = newIdx; // keep RTL on the exact bar
 //StartAnchor.SlotIndex = _lastSIdx ?? sIdx; // (optional) stamp P1 as well
 
 rtlEndPointX = newIdx;
 rtlEndPointPrice = price;
 
 _lastEIdx = newIdx;
 lineSlope = slope;
 }
 finally
 {
 _isExtending = false;
 }
 
 PrintDebug("Bar id " + currIdx + " Extend from " + currIdx + " to " + newIdx + " End Anchor Time " + EndAnchor.Time + " EndANchor price " + EndAnchor.Price);
 CalculateLTLCoordinates(chartControl, chartScale);
 //DeferInvalidate(chartControl);
 RequestRepaint(chartControl);
 }
 
 private bool TryGetBarsAndIndices(
 ChartControl chartControl, ChartScale chartScale,
 out ChartBars bars, out int startIndex, out int endIndex)
 {
 bars = null; startIndex = endIndex = -1;
 
 bars = GetBarsForAnchors(chartControl);
 
 if (bars == null || bars.Count == 0) return false;
 
 startIndex = IndexAtOrBefore(bars, chartControl, StartAnchor.Time);
 endIndex = IndexAtOrBefore(bars, chartControl, EndAnchor.Time);
 
 if (startIndex < 0 || endIndex < 0 || startIndex == endIndex) return false;
 return true;
 }
 
 private int? FindP3Index(ChartBars bars, int startIndex, int endIndex, double slope, double startPrice)
 {
 var series = bars.Bars;
 int lo = Math.Min(startIndex, endIndex) + 1;
 int hi = Math.Max(startIndex, endIndex);
 
 for (int i = lo; i <= hi && i < bars.Count; i++)
 {
 double expected = startPrice + slope * (i - startIndex);
 double barHigh = series.GetHigh(i);
 double barLow = series.GetLow(i);
 if (expected >= barLow && expected <= barHigh)
 return i;
 }
 return null;
 }
 
 private int FindP2Index(ChartBars bars, int startIndex, int p3Index, bool isUp)
 {
 var series = bars.Bars;
 double extreme = isUp ? double.MinValue : double.MaxValue;
 int p2 = -1;
 
 for (int i = startIndex; i < p3Index; i++)
 {
 double v = isUp ? series.GetHigh(i) : series.GetLow(i);
 if ((isUp && v > extreme) || (!isUp && v < extreme))
 {
 extreme = v;
 p2 = i;
 }
 }
 return p2;
 }
 
 private void CalculateLTLCoordinates(ChartControl chartControl, ChartScale chartScale)
 {
 if (!TryGetBarsAndIndices(chartControl, chartScale, out var bars, out int sIdx, out int eIdx))
 return;
 
 var series = bars.Bars;
 if (series == null || bars.Count <= 0) return;
 
 int count = bars.Count;
 sIdx = Math.Max(0, Math.Min(sIdx, count - 1));
 eIdx = Math.Max(0, Math.Min(eIdx, count - 1));
 if (sIdx == eIdx) return;
 
 bool newIsUp = EndAnchor.Price >= StartAnchor.Price;
 bool editingNow = (DrawingState == DrawingState.Editing || DrawingState == DrawingState.Building);
 
 // keep slope stable when not editing (prevents veer)
 double newSlope = (!editingNow && _lastSIdx.HasValue && _lastEIdx.HasValue)
    ? _lastSlope
    : (EndAnchor.Price - StartAnchor.Price) / Math.Max(1, (eIdx - sIdx));
 
 // —— keep P3 stable while extending ——
 int? p3 = _lastP3Idx;
 
 // Keep P3 steady while extending AND while adjusting RTL with P2 locked.
 // If it no longer lies on the new slope inside its bar's hi/lo, we fall back to re-find it.
 bool tryKeepP3 = (!editingNow && p3.HasValue);
 
 //if (!editingNow && p3.HasValue && p3.Value >= sIdx && p3.Value <= eIdx)
 if (tryKeepP3 && p3.Value >= sIdx && p3.Value <= eIdx)
 {
 double expectedAtP3 = StartAnchor.Price + newSlope * (p3.Value - sIdx);
 double hiP3 = series.GetHigh(p3.Value);
 double loP3 = series.GetLow(p3.Value);
 if (!(expectedAtP3 >= loP3 && expectedAtP3 <= hiP3))
 p3 = FindP3Index(bars, sIdx, eIdx, newSlope, StartAnchor.Price);
 }
 else
 {
 p3 = FindP3Index(bars, sIdx, eIdx, newSlope, StartAnchor.Price);
 }
 if (!p3.HasValue) 
 {
	 // keep the previous geometry while there’s no intersecting bar yet
    // (do NOT clear `segments`; just bail after updating cached slope/s/e indices)
    _lastSIdx = sIdx;
    _lastEIdx = eIdx;
    _lastSlope = newSlope;
	 return;
 }
 
 int p2;
 // Keep P2 only while dragging the RTL end, and only if P2 still lies in [sIdx, p3)
 bool keepP2 =
 _keepP2ThisPass && // only for this operation
 _lastP2Idx.HasValue &&
 _lastP2Idx.Value >= sIdx &&
 _lastP2Idx.Value < p3.Value; // must remain strictly before P3
 
 if (keepP2)
 {
 p2 = _lastP2Idx.Value;
 PrintDebug($"P2 kept (scoped) at {p2}");
 }
 else
 {
 p2 = FindP2Index(bars, sIdx, p3.Value, newIsUp);
 if (p2 < 0 || p2 >= count) return;
 PrintDebug($"P2 recalculated to {p2}");
 }
 
 PrintDebug(keepP2 ? $"P2 frozen at {p2}" : $"P2 recalculated to {p2}");
 
 var newSegs = new List<Seg>();
 {
 int origin = p2;
 double currentStartPrice = newIsUp ? series.GetHigh(p2) : series.GetLow(p2);
 int ltlStartX = origin;
 double ltlStartY = currentStartPrice;
 
 int eLimit = Math.Min(eIdx, count - 1);
 for (int i = origin; i <= eLimit; i++)
 {
 if (i < 0 || i >= count) break;
 
 double expected = currentStartPrice + newSlope * (i - origin);
 double hi = series.GetHigh(i);
 double lo = series.GetLow(i);
 bool broken = newIsUp ? (hi > expected) : (lo < expected);
 
 if (broken)
 {
 newSegs.Add(new Seg(ltlStartX, ltlStartY, i, expected));
 origin = i;
 currentStartPrice = newIsUp ? hi : lo;
 ltlStartX = origin;
 ltlStartY = currentStartPrice;
 }
 }
 if (origin != eIdx) {
 double finalExpected = currentStartPrice + newSlope * (eIdx - origin);
 newSegs.Add(new Seg(ltlStartX, ltlStartY, eIdx, finalExpected));
 }
 }
 
 segments.Clear();
 segments.AddRange(newSegs);
 
 isUpContainer = newIsUp;
 lineSlope = newSlope;
 _lastP2Idx = p2;
 _lastP3Idx = p3.Value;
 
 _lastSIdx = sIdx;
 _lastEIdx = eIdx;
 _lastSlope = newSlope;
 
 UpdateVeAnchorsFromLastSegment(chartControl);
 
 PrintDebug($"RTL eIdx={_lastEIdx} EndAnchor.SlotIndex={EndAnchor.SlotIndex} VE eIdx={VeEndAnchor.SlotIndex}");
 
 
 // NEW: pin anchors to their exact bars to avoid time rounding drift
 StartAnchor.Time = bars.GetTimeByBarIdx(chartControl, sIdx);
 EndAnchor.Time   = bars.GetTimeByBarIdx(chartControl, eIdx);
 StartAnchor.SlotIndex = sIdx;
 EndAnchor.SlotIndex = eIdx;
 
 rtlEndPointX = eIdx; // NEW: keep the runtime cache in sync
 rtlEndPointPrice = EndAnchor.Price; // NEW
 }
 
 protected override void OnStateChange()
 {
 if (State == State.SetDefaults)
 { 
 LineStroke = new Stroke(Brushes.DarkGray, DashStyleHelper.Solid, 2f);
 Description = "";
 DrawingState = DrawingState.Building;
 Name = "CustomLine";
 UpBrush = System.Windows.Media.Brushes.Blue;
 DownBrush = System.Windows.Media.Brushes.Red;
 AutoExtend = false;
 ExtendBreakRule = BreakMode.HighLowPenetration;
 AutoExtendIntervalMs = 250;
 DebugLogs = false; // off by default
 
 StartAnchor = new ChartAnchor
 {
 IsBrowsable = true,
 IsEditing = true,
 DrawingTool = this,
 DisplayName = Custom.Resource.NinjaScriptDrawingToolAnchorStart,
 };
 
 EndAnchor = new ChartAnchor
 {
 IsBrowsable = true,
 IsEditing = true,
 DrawingTool = this,
 DisplayName = Custom.Resource.NinjaScriptDrawingToolAnchorEnd,
 };
 
 VeStartAnchor = new ChartAnchor
 {
 IsBrowsable = false,
 IsEditing = false,
 DrawingTool = this,
 DisplayName = Custom.Resource.NinjaScriptDrawingToolAnchorStart,
 };
 
 VeEndAnchor = new ChartAnchor
 {
 IsBrowsable = false,
 IsEditing = false,
 DrawingTool = this,
 DisplayName = Custom.Resource.NinjaScriptDrawingToolAnchorEnd,
 };
 }
 else if (State == State.Configure)
 {
 if (UpBrush == null) UpBrush = Brushes.Blue;
 if (DownBrush == null) DownBrush = Brushes.Red;
 
 anchorPanelIndex = PanelIndex;
 segments.Clear();
 }
 else if (State == State.Active)
 {
 var cp = ChartPanel;
 var cc = cp?.ChartControl;
 var cs = ResolveScale(cc, cp, null);
 if (cc != null && cs != null && StartAnchor != null && EndAnchor != null &&
 !StartAnchor.IsEditing && !EndAnchor.IsEditing)
 {
 try { CalculateLTLCoordinates(cc, cs); }
 catch (Exception ex) { Print("State.Active recalc error: " + ex.Message); }
 }
 
 var barsSeed = GetBarsForAnchors(cc);
 if (barsSeed != null) {
 _lastEIdx = IndexAtOrBefore(barsSeed, cc, EndAnchor.Time);
 rtlEndPointX = _lastEIdx.Value;
 }
 
 EnsureAutoTimer();
 
 if (AutoExtend) StartAutoExtend();
 }
 else if (State == State.Terminated)
 {
 if (activeChartControl != null)
 UnsetContextMenuHandlers();
 
 if (_autoTimer != null)
 {
 _autoTimer.Tick -= AutoTimer_Tick;
 _autoTimer.Stop();
 _autoTimer = null;
 _autoRunning = false;
 }
 
 Dispose();
 }
 }
 
 private void SetContextMenuHandlers(ChartControl chartControl, ChartScale chartScale)
 {
 if (chartControl == null)
 {
 PrintDebug("SetContextMenuHandlers: chartControl is null");
 return;
 }
 if (chartScale == null)
 {
 PrintDebug("SetContextMenuHandlers: chartScale is null");
 return;
 }
 
 if (activeChartControl == chartControl)
 {
 PrintDebug("SetContextMenuHandlers: ChartControl already set, skipping handler attachment");
 return;
 }
 
 PrintDebug("SetContextMenuHandlers: Setting up handlers for new ChartControl");
 
 UnsetContextMenuHandlers();
 
 activeChartControl = chartControl;
 
 if (previewKeyDownHandler == null)
 previewKeyDownHandler = new KeyEventHandler(ChartControl_PreviewKeyDown);
 
 try
 {
 menuItem1 = new MenuItem { Header = "Extend Container", Name = "menuItem1_" };
 menuItem1.InputGestureText = "Ctrl+R";
 menuItem1.Command = extendCommand;
 
 menuItem1.Click += (s, e) =>
 {
 if (IsSelected)
 {
 TryExtendRTL();
 }
 };
 
 menuItem2 = new MenuItem { Header = "Automatically Extend Container", Name = "menuItem2_" };
 menuItem2.IsCheckable = true;
 menuItem2.IsChecked = AutoExtend;
 menuItem2.Click += (s, e) =>
 {
 AutoExtend = menuItem2.IsChecked;
 if (AutoExtend) StartAutoExtend(); else StopAutoExtend();
 };
 
 menuItemNumbers = new MenuItem
 {
 Header = "Toggle Numbers",
 Name = "menuItemNumbers_",
 IsCheckable = true,
 IsChecked = _showNumbers,
 InputGestureText = "Ctrl+W",
 };
 
 menuItemNumbers.Click += (s, e) =>
 {
 _showNumbers = !_showNumbers;
 menuItemNumbers.IsChecked = _showNumbers;
 menuItemNumbers.IsEnabled = IsSelected;
 //DeferInvalidate(activeChartControl);
	 RequestRepaint(activeChartControl);
 };
 
 menuItemStyle = new MenuItem { Header = "Cycle Line Style", InputGestureText = "Ctrl+Q" };
 menuItemStyle.Click += (s, e) => { if (IsSelected) CycleLineStyle(); };
 //items.Add(menuItemStyle);
 
 Action attach = () =>
 {
 contextMenuOpeningHandler = (sender, e) => ChartControl_ContextMenuOpening(sender, e);
 contextMenuClosingHandler = (sender, e) => ChartControl_ContextMenuClosing(sender, e);
 activeChartControl.ContextMenuOpening += contextMenuOpeningHandler;
 activeChartControl.ContextMenuClosing += contextMenuClosingHandler;
 
 // Control-level (fires when the chart control has focus)
 if (keyBindingCtrlR_Control != null)
 activeChartControl.InputBindings.Remove(keyBindingCtrlR_Control);
 
 keyBindingCtrlR_Control = new KeyBinding(extendCommand, new KeyGesture(Key.R, ModifierKeys.Control));
 activeChartControl.InputBindings.Add(keyBindingCtrlR_Control);
 PrintDebug("Attached KeyBinding Ctrl+R at control level");
 
 if (previewKeyDownHandler == null)
 previewKeyDownHandler = (sender, e) => ChartControl_PreviewKeyDown(sender, e);
 activeChartControl.PreviewKeyDown += previewKeyDownHandler;
 
 if (extendCommandBinding != null)
 activeChartControl.CommandBindings.Remove(extendCommandBinding);
 
 extendCommandBinding = new CommandBinding(
 extendCommand,
 (s, e) =>
 {
 if (IsSelected)
 {
 PrintDebug("Ctrl+R / Menu Command executed (control-level)");
 TryExtendRTL();
 e.Handled = true;
 }
 },
 (s, e) => { e.CanExecute = IsSelected; });
 
 activeChartControl.CommandBindings.Add(extendCommandBinding);
 
 var cw = Window.GetWindow(activeChartControl);
 if (cw != null)
 {
 activeChartWindow = cw;
 
 if (windowPreviewKeyDownHandler == null)
 windowPreviewKeyDownHandler = new KeyEventHandler(ChartWindow_PreviewKeyDown);
 
 activeChartWindow.AddHandler(Keyboard.PreviewKeyDownEvent, windowPreviewKeyDownHandler, /*handledEventsToo*/ true);
 
 if (extendCommandBindingWin != null)
 cw.CommandBindings.Remove(extendCommandBindingWin);
 
 extendCommandBindingWin = new CommandBinding(
 extendCommand,
 (s, e) =>
 {
 if (IsSelected)
 {
 PrintDebug("Ctrl+R executed (window-level)");
 TryExtendRTL();
 e.Handled = true;
 }
 },
 (s, e) => { e.CanExecute = IsSelected; });
 
 cw.CommandBindings.Add(extendCommandBindingWin);
 }
 else
 {
 PrintDebug("SetContextMenuHandlers: ChartWindow is null; relying on control PreviewKeyDown");
 }
 };
 
 if (activeChartControl.Dispatcher.CheckAccess())
 attach();
 else
 activeChartControl.Dispatcher.Invoke(attach);
 
 // Window-level (fires even when focus is inside other elements)
 if (activeChartWindow != null)
 {
 if (keyBindingCtrlR_Window != null)
 activeChartWindow.InputBindings.Remove(keyBindingCtrlR_Window);
 
 // Use a separate instance for the window (a Binding can't be owned by two parents)
 keyBindingCtrlR_Window = new KeyBinding(extendCommand, new KeyGesture(Key.R, ModifierKeys.Control));
 activeChartWindow.InputBindings.Add(keyBindingCtrlR_Window);
 PrintDebug("Attached KeyBinding Ctrl+R at window level");
 }
 }
 catch (Exception ex)
 {
 PrintDebug($"SetContextMenuHandlers: Exception - {ex.Message}");
 }
 }
 
 private void UnsetContextMenuHandlers()
 {
 var cc = activeChartControl;
 var cw = activeChartWindow;
 
 PrintDebug("UnsetContextMenuHandlers: Cleaning up handlers");
 
 try
 {
 Action detach = () =>
 {
 if (cc != null && keyBindingCtrlR_Control != null)
 {
 try
 {
 cc.InputBindings.Remove(keyBindingCtrlR_Control);
 PrintDebug("Removed control KeyBinding Ctrl+R");
 }
 catch { /* ignore */ }
 
 keyBindingCtrlR_Control = null;
 if (contextMenuOpeningHandler != null)
 {
 cc.ContextMenuOpening -= contextMenuOpeningHandler;
 PrintDebug("Detached ContextMenuOpening handler");
 }
 if (contextMenuClosingHandler != null)
 {
 cc.ContextMenuClosing -= contextMenuClosingHandler;
 PrintDebug("Detached ContextMenuClosing handler");
 }
 
 var cm = cc.ContextMenu;
 if (cm != null)
 {
 if (menuItem1 != null && cm.Items.Contains(menuItem1))
 {
 cm.Items.Remove(menuItem1);
 PrintDebug("Removed menuItem1");
 }
 if (menuItem2 != null && cm.Items.Contains(menuItem2))
 {
 cm.Items.Remove(menuItem2);
 PrintDebug("Removed menuItem2");
 }
 if (menuItemNumbers != null && cm.Items.Contains(menuItemNumbers))
 {
 cm.Items.Remove(menuItemNumbers);
 PrintDebug("Removed menuItemNumbers");
 }
 if (menuItemStyle != null && cm.Items.Contains(menuItemStyle)) 
 {
 cm.Items.Remove(menuItemStyle);
 PrintDebug("Removed menuItemStyle");
 }
 }
 
 if (extendCommandBinding != null)
 {
 cc.CommandBindings.Remove(extendCommandBinding);
 PrintDebug("Removed control CommandBinding");
 }
 
 if (previewKeyDownHandler != null)
 {
 cc.RemoveHandler(Keyboard.PreviewKeyDownEvent, previewKeyDownHandler);
 PrintDebug("Removed control PreviewKeyDown (handledEventsToo) handler");
 }
 
 if (cw != null && windowPreviewKeyDownHandler != null)
 {
 cw.RemoveHandler(Keyboard.PreviewKeyDownEvent, windowPreviewKeyDownHandler);
 PrintDebug("Removed window PreviewKeyDown (handledEventsToo) handler");
 }
 }
 
 if (cw != null && keyBindingCtrlR_Window != null)
 {
 try
 {
 cw.InputBindings.Remove(keyBindingCtrlR_Window);
 PrintDebug("Removed window KeyBinding Ctrl+R");
 }
 catch { /* ignore */ }
 keyBindingCtrlR_Window = null;
 
 if (extendCommandBindingWin != null)
 {
 cw.CommandBindings.Remove(extendCommandBindingWin);
 PrintDebug("Removed window CommandBinding");
 }
 }
 };
 
 if (cc != null)
 {
 if (cc.Dispatcher.CheckAccess()) detach();
 else cc.Dispatcher.Invoke(detach);
 }
 else if (cw != null)
 {
 if (cw.Dispatcher.CheckAccess()) detach();
 else cw.Dispatcher.Invoke(detach);
 }
 }
 catch (Exception ex)
 {
 PrintDebug($"UnsetContextMenuHandlers: Exception - {ex.Message}");
 }
 
 activeChartControl = null;
 activeChartWindow = null;
 
 contextMenuOpeningHandler = null;
 contextMenuClosingHandler = null;
 previewKeyDownHandler = null;
 
 menuItem1 = null;
 menuItem2 = null;
 
 extendCommandBinding = null;
 extendCommandBindingWin = null;
 
 menuItemNumbers = null;
 menuItemStyle = null;
 }
 
 private void ChartWindow_PreviewKeyDown(object sender, KeyEventArgs e)
 {
 if (!IsSelected) return;
 
 if (HandleStyleWidthHotkeys(e)) return;
 
 //if (e.Key == Key.R && Keyboard.Modifiers == ModifierKeys.Control)
 if (e.Key == Key.R && Keyboard.Modifiers == ModifierKeys.Control &&
 (keyBindingCtrlR_Control != null || keyBindingCtrlR_Window != null))
 {
 if (_isExtending || e.IsRepeat) { e.Handled = true; return; }
 PrintDebug("CTRL+R (Window Preview handled) -> TryExtendRTL()");
 TryExtendRTL();
 e.Handled = true;
 }
 }
 
 private void ChartControl_PreviewKeyDown(object sender, KeyEventArgs e)
 {
 if (!IsSelected) return;
 
 if (HandleStyleWidthHotkeys(e)) return;
 
 //if (e.Key == Key.R && Keyboard.Modifiers == ModifierKeys.Control)
 // Let the KeyBinding handle Ctrl+R if we installed it
 if (e.Key == Key.R && Keyboard.Modifiers == ModifierKeys.Control &&
 (keyBindingCtrlR_Control != null || keyBindingCtrlR_Window != null))
 {
 if (_isExtending || e.IsRepeat) { e.Handled = true; return; }
 PrintDebug("CTRL+R (Preview) -> TryExtendRTL()");
 TryExtendRTL();
 e.Handled = true;
 return;
 }
 
 if (e.Key == Key.W && Keyboard.Modifiers == ModifierKeys.Control)
 {
 _showNumbers = !_showNumbers;
 //DeferInvalidate(activeChartControl);
	 RequestRepaint(activeChartControl);
 e.Handled = true;
 return;
 }
 }
 
 private void TryExtendRTL()
 {
 var cc = activeChartControl;
 if (cc == null) { PrintDebug("activeChartControl is null"); return; }
 
 if (_hotkeyGate) { PrintDebug("Extend ignored: same key press already handled"); return; }
 _hotkeyGate = true;
 
 try
 {
 if (anchorPanelIndex < 0 || anchorPanelIndex >= cc.ChartPanels.Count)
 { PrintDebug("anchorPanelIndex is < 0"); return; }
 
 var cp = cc.ChartPanels[anchorPanelIndex];
 var cs = ResolveScale(cc, cp, null);
 if (cs == null) { PrintDebug("chartScale is null"); return; }
 
 _keepP2ThisPass = _lastP2Idx.HasValue; // <- KEEP P2 for this exten
 ExtendRTL(cc, cs);
 }
 finally
 {
 _keepP2ThisPass = false; // <- clear after the recompute
 cc.Dispatcher.BeginInvoke(
 new Action(() => _hotkeyGate = false),
 System.Windows.Threading.DispatcherPriority.Background);
 }
 }
 }
 
 public static partial class Draw
 {
 private static T DrawCustomLineTypeCore<T>(NinjaScriptBase owner, bool isAutoScale, string tag,
 int startBarsAgo, DateTime startTime, double startY, int endBarsAgo, DateTime endTime, double endY,
 Brush brush, DashStyleHelper dashStyle, int width, bool isGlobal, string templateName) where T : CustomLine
 {
 if (owner == null)
 throw new ArgumentException("owner");
 
 if (string.IsNullOrWhiteSpace(tag))
 throw new ArgumentException(@"tag cant be null or empty", "tag");
 
 if (isGlobal && tag[0] != GlobalDrawingToolManager.GlobalDrawingToolTagPrefix)
 tag = string.Format("{0}{1}", GlobalDrawingToolManager.GlobalDrawingToolTagPrefix, tag);
 
 T lineT = DrawingTool.GetByTagOrNew(owner, typeof(T), tag, templateName) as T;
 
 if (lineT == null)
 return null;
 
 if (startTime == Core.Globals.MinDate && endTime == Core.Globals.MinDate && startBarsAgo == int.MinValue && endBarsAgo == int.MinValue)
 throw new ArgumentException("bad start/end date/time");
 
 DrawingTool.SetDrawingToolCommonValues(lineT, tag, isAutoScale, owner, isGlobal);
 
 ChartAnchor startAnchor;
 
 startAnchor = DrawingTool.CreateChartAnchor(owner, startBarsAgo, startTime, startY);
 ChartAnchor endAnchor = DrawingTool.CreateChartAnchor(owner, endBarsAgo, endTime, endY);
 startAnchor.CopyDataValues(lineT.StartAnchor);
 endAnchor.CopyDataValues(lineT.EndAnchor);
 
 if (brush != null)
 lineT.LineStroke = new Stroke(brush, dashStyle, width);
 
 lineT.SetState(State.Active);
 return lineT;
 }
 
 private static CustomLine CustomLine(NinjaScriptBase owner, bool isAutoScale, string tag,
 int startBarsAgo, DateTime startTime, double startY, int endBarsAgo, DateTime endTime, double endY,
 Brush brush, DashStyleHelper dashStyle, int width)
 {
 return DrawCustomLineTypeCore<CustomLine>(owner, isAutoScale, tag, startBarsAgo, startTime, startY, endBarsAgo, endTime, endY, brush, dashStyle, width, false, null);
 }
 
 /// <summary>
 /// Draws a line between two points.
 /// </summary>
 public static CustomLine CustomLine(NinjaScriptBase owner, string tag, int startBarsAgo, double startY, int endBarsAgo, double endY, Brush brush)
 {
 return CustomLine(owner, false, tag, startBarsAgo, Core.Globals.MinDate, startY, endBarsAgo, Core.Globals.MinDate, endY, brush, DashStyleHelper.Solid, 1);
 }
 }
 }