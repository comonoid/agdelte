/**
 * Agdelte Runtime - Main Entry Point
 * Запускает Elm-подобное приложение в браузере
 */

import { createElement, patch } from './dom.js';
import { subscribe, unsubscribe, diffEvents } from './events.js';

/**
 * Запуск приложения
 * @param {Object} app - Скомпилированное Agda приложение
 * @param {HTMLElement} container - DOM контейнер
 * @returns {Object} - API для управления приложением
 */
export function runApp(app, container) {
  // Состояние приложения
  let model = app.init;
  let currentVdom = null;
  let currentDom = null;
  let activeSubscriptions = new Map();
  let isUpdating = false;
  let pendingMessages = [];

  // Диспетчер сообщений
  function dispatch(msg) {
    if (isUpdating) {
      // Накапливаем сообщения во время обновления
      pendingMessages.push(msg);
      return;
    }

    isUpdating = true;

    try {
      // Обновляем модель
      model = app.update(msg)(model);

      // Перерисовываем
      render();

      // Обновляем подписки
      updateSubscriptions();

      // Обрабатываем накопленные сообщения
      while (pendingMessages.length > 0) {
        const nextMsg = pendingMessages.shift();
        model = app.update(nextMsg)(model);
        render();
        updateSubscriptions();
      }
    } finally {
      isUpdating = false;
    }
  }

  // Рендеринг
  function render() {
    const newVdom = app.view(model);

    if (currentDom === null) {
      // Первый рендер
      currentDom = createElement(newVdom, dispatch);
      container.appendChild(currentDom);
    } else {
      // Патчинг
      currentDom = patch(currentDom, currentVdom, newVdom, dispatch);
    }

    currentVdom = newVdom;
  }

  // Обновление подписок на события
  function updateSubscriptions() {
    const newEvents = app.events(model);
    const diff = diffEvents(activeSubscriptions, newEvents);

    // Отписываемся от старых
    for (const [key, sub] of diff.removed) {
      unsubscribe(sub);
      activeSubscriptions.delete(key);
    }

    // Подписываемся на новые
    for (const [key, eventSpec] of diff.added) {
      const sub = subscribe(eventSpec, dispatch);
      activeSubscriptions.set(key, sub);
    }
  }

  // Получение событий из Signal (List Msg)
  function processEventSignal(eventSignal) {
    // Event = Signal (List Msg)
    // now : List Msg — события на текущем такте
    const messages = eventSignal.now;

    if (Array.isArray(messages)) {
      for (const msg of messages) {
        dispatch(msg);
      }
    }

    return eventSignal.next;
  }

  // Запуск тиков (requestAnimationFrame или setInterval)
  let tickHandle = null;
  let eventSignal = null;

  function startTicking() {
    eventSignal = app.events(model);

    function tick() {
      if (eventSignal) {
        eventSignal = processEventSignal(eventSignal);
      }
      tickHandle = requestAnimationFrame(tick);
    }

    tickHandle = requestAnimationFrame(tick);
  }

  function stopTicking() {
    if (tickHandle !== null) {
      cancelAnimationFrame(tickHandle);
      tickHandle = null;
    }
  }

  // Инициализация
  render();
  updateSubscriptions();
  // startTicking(); // Включить для автоматических тиков

  // Публичный API
  return {
    // Отправить сообщение
    dispatch,

    // Получить текущую модель
    getModel: () => model,

    // Получить текущий DOM
    getContainer: () => container,

    // Принудительный ререндер
    forceRender: render,

    // Управление тиками
    start: startTicking,
    stop: stopTicking,

    // Уничтожение приложения
    destroy: () => {
      stopTicking();
      for (const sub of activeSubscriptions.values()) {
        unsubscribe(sub);
      }
      activeSubscriptions.clear();
      container.innerHTML = '';
    }
  };
}

/**
 * Инициализация приложения при загрузке DOM
 */
export function mount(app, selector = '#app') {
  const container = document.querySelector(selector);
  if (!container) {
    throw new Error(`Container not found: ${selector}`);
  }
  return runApp(app, container);
}

/**
 * Горячая перезагрузка (для разработки)
 */
export function hotReload(appInstance, newApp) {
  const model = appInstance.getModel();
  const container = appInstance.getContainer();

  appInstance.destroy();

  // Создаём новое приложение с сохранённой моделью
  const modifiedApp = {
    ...newApp,
    init: model
  };

  return runApp(modifiedApp, container);
}

// Экспорт для использования в браузере
if (typeof window !== 'undefined') {
  window.Agdelte = { runApp, mount, hotReload };
}
